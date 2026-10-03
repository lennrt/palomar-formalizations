// Exhaustive isolate-anchored search for small dominating sets of the folded
// even orthogonality graph Omega_n (n divisible by four). C++17, exact integer
// arithmetic, no optimizer and no randomness.
//
// Vertices are antipodal classes of even-weight n-bit words, represented by
// the even words whose top bit is zero. Two distinct classes are adjacent at
// Hamming distance n/2.  A candidate dominating set has 1 + t + 2 centres:
//   * the class of the zero word (after an even translation);
//   * t "rows", enumerated up to coordinate permutations as weak compositions
//     of n into 2^t column patterns;
//   * two completing centres found by exact propagation: the first uncovered
//     class x0 must be dominated by one of them, which therefore lies in the
//     closed neighbourhood N[x0]; the final centre must lie in the intersection
//     of the closed neighbourhoods of every class that is still uncovered.
//
// anchored = 1 additionally uses the theorem that every dominating set with
// fewer than n/2 vertices has an isolated selected vertex (ABCO parity lemma).
// Translating that vertex to zero, every other centre has weight different
// from 0, n/2 and n; class representatives are chosen with even weight in
// [2, n/2-2], and the enumerated rows are listed in nondecreasing weight.
// anchored = 0 makes no such assumption (rows of even weight at most n/2).
//
// Usage: folded_cube_anchored n t anchored [threads]
#include <atomic>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <mutex>
#include <thread>
#include <vector>
using namespace std;

static int n, t, anchored;
static uint32_t full;
static int V, W;
static vector<uint32_t> reps;
static vector<int> cls;
static vector<uint64_t> NB;          // closed-neighbourhood bitsets
static vector<vector<int>> nbl;      // closed-neighbourhood lists
static vector<vector<uint32_t>> orbits;
static unsigned long long compositions = 0, even_compositions = 0;

static inline int wt(uint32_t x) { return __builtin_popcount(x); }

static void enumerate(int pattern, int remaining, int position, vector<uint32_t>& rows) {
    const int patterns = 1 << t;
    if (pattern == patterns - 1) {
        vector<uint32_t> w = rows;
        const uint32_t block = (remaining ? ((1u << remaining) - 1) : 0u) << position;
        for (int r = 0; r < t; ++r) w[r] |= block;
        ++compositions;
        for (int r = 0; r < t; ++r) if (wt(w[r]) & 1) return;
        ++even_compositions;
        int previous = 0;
        for (int r = 0; r < t; ++r) {
            const int x = wt(w[r]);
            if (anchored) { if (x < 2 || x > n / 2 - 2) return; }
            else if (x > n / 2) return;
            if (x < previous) return;
            previous = x;
        }
        orbits.push_back(w);
        return;
    }
    for (int c = 0; c <= remaining; ++c) {
        vector<uint32_t> w = rows;
        const uint32_t block = (c ? ((1u << c) - 1) : 0u) << position;
        for (int r = 0; r < t; ++r) if (pattern & (1 << r)) w[r] |= block;
        enumerate(pattern + 1, remaining - c, position + c, w);
    }
}

int main(int argc, char** argv) {
    if (argc < 4) { fprintf(stderr, "usage: n t anchored [threads]\n"); return 2; }
    n = atoi(argv[1]); t = atoi(argv[2]); anchored = atoi(argv[3]);
    const int threads = argc > 4 ? atoi(argv[4]) : 8;
    if (n % 4 || n < 4 || n > 20 || t < 0 || t > 4) { fprintf(stderr, "bad parameters\n"); return 2; }
    full = (1u << n) - 1;
    for (uint32_t x = 0; x < (1u << (n - 1)); ++x) if (wt(x) % 2 == 0) reps.push_back(x);
    V = (int)reps.size(); W = (V + 63) / 64;
    cls.assign(1u << n, -1);
    for (int j = 0; j < V; ++j) { cls[reps[j]] = j; cls[reps[j] ^ full] = j; }
    NB.assign((size_t)V * W, 0); nbl.resize(V);
    for (int i = 0; i < V; ++i) for (int j = 0; j < V; ++j) {
        const int d = wt(reps[i] ^ reps[j]);
        if (d == 0 || d == n / 2 || d == n) {
            NB[(size_t)i * W + j / 64] |= 1ull << (j % 64);
            nbl[i].push_back(j);
        }
    }
    if (t > 0) { vector<uint32_t> rows(t, 0); enumerate(0, n, 0, rows); }
    else orbits.push_back({});
    atomic<size_t> next(0);
    atomic<long long> candidates(0), solutions(0), least(V);
    mutex guard; vector<uint32_t> example;
    auto worker = [&]() {
        vector<uint64_t> U(W), U2(W), C(W);
        for (;;) {
            const size_t o = next.fetch_add(1);
            if (o >= orbits.size()) break;
            const auto& rows = orbits[o];
            for (int q = 0; q < W; ++q) {
                uint64_t m = NB[q];                       // class of the zero word is index 0
                for (uint32_t b : rows) m |= NB[(size_t)cls[b] * W + q];
                U[q] = ~m;
            }
            if (V % 64) U[W - 1] &= (1ull << (V % 64)) - 1;
            int x0 = -1;
            for (int q = 0; q < W && x0 < 0; ++q) if (U[q]) x0 = q * 64 + __builtin_ctzll(U[q]);
            if (x0 < 0) {
                ++solutions; lock_guard<mutex> lock(guard);
                if (example.empty()) { example = rows; }
                continue;
            }
            for (int c : nbl[x0]) {
                if (anchored) { const int x = wt(reps[c]); if (x == 0 || x == n / 2) continue; }
                ++candidates;
                const uint64_t* Nc = &NB[(size_t)c * W];
                int count = 0;
                for (int q = 0; q < W; ++q) { U2[q] = U[q] & ~Nc[q]; count += __builtin_popcountll(U2[q]); }
                long long current = least.load();
                while (count < current && !least.compare_exchange_weak(current, count)) {}
                bool ok;
                if (count == 0) ok = true;
                else if (count > (int)nbl[0].size()) ok = false;
                else {
                    bool started = false; ok = true;
                    for (int q = 0; q < W && ok; ++q) {
                        uint64_t m = U2[q];
                        while (m) {
                            const int x = q * 64 + __builtin_ctzll(m); m &= m - 1;
                            const uint64_t* Nx = &NB[(size_t)x * W];
                            if (!started) { for (int z = 0; z < W; ++z) C[z] = Nx[z]; started = true; }
                            else {
                                uint64_t any = 0;
                                for (int z = 0; z < W; ++z) { C[z] &= Nx[z]; any |= C[z]; }
                                if (!any) { ok = false; break; }
                            }
                        }
                    }
                    if (ok && anchored) {
                        bool good = false;
                        for (int z = 0; z < W && !good; ++z) {
                            uint64_t m = C[z];
                            while (m) {
                                const int x = z * 64 + __builtin_ctzll(m); m &= m - 1;
                                const int wx = wt(reps[x]);
                                if (wx != 0 && wx != n / 2) { good = true; break; }
                            }
                        }
                        ok = good;
                    }
                }
                if (ok) {
                    ++solutions; lock_guard<mutex> lock(guard);
                    if (example.empty()) { example = rows; example.push_back(reps[c]); }
                }
            }
        }
    };
    vector<thread> pool;
    for (int i = 0; i < threads; ++i) pool.emplace_back(worker);
    for (auto& th : pool) th.join();
    printf("{\"method\":\"anchored_bitset\",\"n\":%d,\"centres\":%d,\"anchored\":%d,"
           "\"classes\":%d,\"closed_neighbourhood\":%zu,\"compositions\":%llu,"
           "\"even_row_compositions\":%llu,\"row_orbits\":%zu,"
           "\"second_last_centre_candidates\":%lld,\"completions_found\":%lld,"
           "\"least_uncovered_before_last_centre\":%lld",
           n, 1 + t + 2, anchored, V, nbl[0].size(), compositions, even_compositions,
           orbits.size(), (long long)candidates, (long long)solutions, (long long)least);
    if (!example.empty()) {
        printf(",\"partial_example\":[0");
        for (uint32_t b : example) printf(",%u", b);
        printf("]");
    }
    printf("}\n");
    return 0;
}
