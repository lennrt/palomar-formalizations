"""Independent literal-bag verification of the final split-edge construction."""
from collections import defaultdict
from itertools import combinations, combinations_with_replacement, product
import json
from grid_sensors import placement,bag,check


def corner_collision_audit(n):
    sensors=sorted(placement(n)); vertices=list(product(range(n),repeat=2))
    corners=[(0,0),(n-1,n-1),(0,n-1),(n-1,0)]
    groups=defaultdict(list)
    for pop in combinations_with_replacement(vertices,2):
        signature=tuple(bag(pop,s)for s in corners)
        for i in (0,2):
            assert tuple(sorted(2*(n-1)-d for d in signature[i]))==signature[i+1]
        groups[signature].append(pop)
    checked=0
    for group in groups.values():
        reports=[tuple(bag(pop,s)for s in sensors)for pop in group]
        compressed=[tuple(r if s in corners else sum(r)
                          for s,r in zip(sensors,report)) for report in reports]
        for x,y in combinations(reports,2):
            assert sum(a!=b for a,b in zip(x,y))>=2
            checked+=1
        for x,y in combinations(compressed,2):
            assert sum(a!=b for a,b in zip(x,y))>=2
    return checked


def literal_all_population_audit(n):
    vertices=list(product(range(n),repeat=2)); sensors=sorted(placement(n))
    corners={(0,0),(n-1,n-1),(0,n-1),(n-1,0)}
    populations=[()]+[(v,)for v in vertices]+list(combinations_with_replacement(vertices,2))
    reports=[tuple(bag(pop,s)for s in sensors)for pop in populations]
    compressed=[tuple(r if s in corners else sum(r)
                      for s,r in zip(sensors,report)) for report in reports]
    minimum=len(sensors)
    for a,b in combinations(reports,2):
        minimum=min(minimum,sum(x!=y for x,y in zip(a,b)))
    assert minimum>=2
    minimum_compressed=min(sum(x!=y for x,y in zip(a,b))
                           for a,b in combinations(compressed,2))
    assert minimum_compressed>=2
    return {'populations':len(populations),'pairs':len(populations)*(len(populations)-1)//2,
            'minimum_separation':minimum,
            'hybrid_moment_minimum_separation':minimum_compressed}


def skinny_audit(n):
    sensors=placement(n);count=0
    for k in range(1,n-1):
        for a,b in product(range(n-1-k),repeat=2):
            xp=((a,b+1),(a+k+1,b+k));yp=((a+1,b),(a+k,b+k+1))
            actual={s for s in sensors if bag(xp,s)!=bag(yp,s)}
            expected={s for s in sensors if (a<s[0]<=a+k)!=(b<s[1]<=b+k)}
            assert actual==expected and len(actual)>=2
            count+=1
    return count


def main():
    rows=[]
    for n in range(6,35):
        s=placement(n);result=check(n,s)
        assert result['robust']
        result.update(n=n,skinny_bag_checks=skinny_audit(n))
        if n<=14:result['corner_collision_pairs']=corner_collision_audit(n)
        rows.append(result)
    full=literal_all_population_audit(6)
    # Without the split anchors, the entire core is a zero-cut ambiguity.
    broken=placement(10)-{(1,0),(0,1)}
    counterexample=check(10,broken)
    assert not counterexample['robust']
    assert len({s for s in broken if bag(counterexample['positive'],s)
                !=bag(counterexample['negative'],s)})<2
    print(json.dumps({'status':'passed','construction':'split-edge reversed stars',
                      'literal_all_mass_at_most_two_n6':full,'orders':rows,
                      'missing_anchors_counterexample':counterexample},indent=2))


if __name__=='__main__':main()
