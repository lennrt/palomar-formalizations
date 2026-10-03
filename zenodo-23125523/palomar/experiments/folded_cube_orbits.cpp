// Exact coordinate-orbit audit of closed-neighborhood covers in Omega_12.
// No optimizer, floating point, or randomized step. Compile with C++17.
// Method 1 enumerates weak compositions recursively and unions neighborhood
// bitsets. Method 2 uses stars-and-bars combinations and literal distances,
// with the opposite coordinate fixed to choose antipodal representatives.
#include <array>
#include <bitset>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <stdexcept>
#include <string>
using namespace std;
constexpr int n = 12, full = (1 << n) - 1, order = 1 << (n - 2);
using Words = array<int,4>;
using Counts = array<int,16>;
array<bitset<order>,1<<n> cover;
uint64_t leaves = 0, even_leaves = 0;
int minimum_missing = order;
Words best_words{};
Counts counts{}, best_counts{};
int weight(int x) { return __builtin_popcount(static_cast<unsigned>(x)); }

void visit(int pattern, int remaining, int position, Words words) {
    if (pattern == 15) {
        const int block = ((1 << remaining) - 1) << position;
        for (int r=0;r<4;++r) words[r] |= block;
        counts[15] = remaining;
        ++leaves;
        for (int w:words) if (weight(w)%2) return;
        ++even_leaves;
        auto seen = cover[0];
        for (int w:words) seen |= cover[w];
        const int missing = order-static_cast<int>(seen.count());
        if (missing < minimum_missing) {
            minimum_missing=missing; best_words=words; best_counts=counts;
        }
        return;
    }
    for (int c=0;c<=remaining;++c) {
        counts[pattern]=c;
        Words next=words;
        const int block=((1<<c)-1)<<position;
        for(int r=0;r<4;++r) if(pattern&(1<<r)) next[r] |= block;
        visit(pattern+1,remaining-c,position+c,next);
    }
}
void bitset_audit() {
    array<int,order> reps{};
    int size=0;
    for(int x=0;x<(1<<(n-1));++x) if(weight(x)%2==0) reps[size++]=x;
    if(size!=order) throw runtime_error("incorrect quotient order");
    for(int x=0;x<=full;++x) if(weight(x)%2==0)
        for(int j=0;j<order;++j)
            if(x==reps[j] || (x^full)==reps[j] || weight(x^reps[j])==n/2)
                cover[x].set(j);
    visit(0,n,0,{});
    if(leaves!=17383860 || even_leaves!=1088100 || minimum_missing!=20)
        throw runtime_error("unexpected exhaustive result");
    cout << "{\"method\":\"recursive_bitset\",\"n\":12,\"maximum_centers\":5,"
         << "\"compositions\":"<<leaves<<",\"even_row_compositions\":"<<even_leaves
         <<",\"minimum_uncovered_classes\":"<<minimum_missing<<",\"witness_centers\":[0";
    for(int w:best_words) cout<<","<<w;
    cout<<"],\"witness_pattern_counts\":[";
    for(int j=0;j<16;++j) { if(j)cout<<","; cout<<best_counts[j]; }
    cout<<"]}\n";
}
void literal_audit() {
    // Separators occupy 15 of the 27 positions. Gaps give sixteen counts.
    array<int,15> bars{};
    for(int i=0;i<15;++i) bars[i]=i;
    array<int,order> reps{};
    int size=0;
    for(int x=0;x<=full;x+=2) if(weight(x)%2==0) reps[size++]=x;
    if(size!=order) throw runtime_error("incorrect alternative quotient order");
    do {
        ++leaves;
        Counts c{};
        int previous=-1;
        for(int j=0;j<15;++j) { c[j]=bars[j]-previous-1; previous=bars[j]; }
        c[15]=26-previous;
        array<int,4> row_weights{};
        for(int p=0;p<16;++p) for(int r=0;r<4;++r)
            row_weights[r] += c[p]*((p>>r)&1);
        bool even=true;
        for(int w:row_weights) if(w%2) even=false;
        if(even) {
            ++even_leaves;
            Words words{};
            int coordinate=0;
            for(int p=0;p<16;++p) for(int j=0;j<c[p];++j,++coordinate)
                for(int r=0;r<4;++r) if((p>>r)&1) words[r] += 1<<coordinate;
            if(coordinate!=12) throw runtime_error("composition total");
            int missing=0;
            for(int x:reps) {
                int d=weight(x);
                if(d==0 || d==6 || d==12) continue;
                bool uncovered=true;
                for(int w:words) {
                    d=weight(x^w);
                    if(d==0 || d==6 || d==12) { uncovered=false; break; }
                }
                if(uncovered && ++missing==20) break;
            }
            if(missing<20) throw runtime_error("fewer than twenty uncovered classes");
        }
        int i=14;
        while(i>=0 && bars[i]==12+i) --i;
        if(i<0) break;
        ++bars[i];
        for(int j=i+1;j<15;++j) bars[j]=bars[j-1]+1;
    } while(true);
    if(leaves!=17383860 || even_leaves!=1088100) throw runtime_error("orbit count");
    cout<<"{\"method\":\"stars_bars_literal\",\"n\":12,\"maximum_centers\":5,"
        <<"\"compositions\":"<<leaves<<",\"even_row_compositions\":"<<even_leaves
        <<",\"verified_uncovered_lower_bound\":20}\n";
}
int main(int argc,char**argv) {
    try {
        if(argc!=2) throw runtime_error("specify bitset or literal");
        if(string(argv[1])=="bitset") bitset_audit();
        else if(string(argv[1])=="literal") literal_audit();
        else throw runtime_error("unknown method");
    } catch(const exception& e) { cerr<<e.what()<<"\n"; return EXIT_FAILURE; }
}
