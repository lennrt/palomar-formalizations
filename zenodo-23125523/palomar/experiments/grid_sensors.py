"""Construct and verify erasure-resilient anonymous grid sensors.

This checks the paper's exact equal-length interval criterion. A failed check
returns an explicit pair of two-target populations whose reports differ at fewer
than two selected sensors. Only the standard library is used.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path


def placement(n: int) -> set[tuple[int, int]]:
    if n < 6:
        raise ValueError('The all-order construction requires n >= 6.')
    m=n-2
    q,r=divmod(m,4)
    sensors={(0,0),(0,n-1),(n-1,0),(n-1,n-1)}
    for i in range(q):
        for t in range(3):
            sensors.add((i+1,3*i+t+1))
            sensors.add((q+3*(q-1-i)+t+1,3*q+i+1))
    sensors.remove((1,1))
    sensors.update({(1,0),(0,1)})
    for i in range(4*q+1,m+1):
        sensors.update({(i,0),(i,n-1),(0,i),(n-1,i)})
    assert len(sensors)==6*q+5+4*r
    return sensors


def bag(population, sensor):
    return tuple(sorted(abs(x-sensor[0])+abs(y-sensor[1]) for x,y in population))


def check(n: int, sensors: set[tuple[int,int]]) -> dict:
    if n < 3:
        raise ValueError('The interval criterion here requires n >= 3.')
    if any(not(0<=x<n and 0<=y<n)for x,y in sensors):
        raise ValueError('Sensor outside the graph.')
    corners={(0,0),(0,n-1),(n-1,0),(n-1,n-1)}
    if not corners<=sensors:
        raise ValueError('This complete criterion requires all four corners.')
    prefix=[[0]*(n+1)for _ in range(n+1)]
    for x in range(n):
        for y in range(n):
            prefix[x+1][y+1]=(int((x,y)in sensors)+prefix[x][y+1]
                              +prefix[x+1][y]-prefix[x][y])
    def rectangle(x0,x1,y0,y1):
        return prefix[x1][y1]-prefix[x0][y1]-prefix[x1][y0]+prefix[x0][y0]
    minimum=len(sensors)
    tested=0
    for k in range(1,n-1):
        for a in range(n-1-k):
            for b in range(n-1-k):
                cut=(rectangle(a+1,a+k+1,0,n)+rectangle(0,n,b+1,b+k+1)
                     -2*rectangle(a+1,a+k+1,b+1,b+k+1))
                tested+=1
                minimum=min(minimum,cut)
                if cut<2:
                    return {'robust':False,'intervals':[[a+1,a+k],[b+1,b+k]],
                            'detectors':cut,'positive':[[a,b+1],[a+k+1,b+k]],
                            'negative':[[a+1,b],[a+k,b+k+1]]}
    return {'robust':True,'sensor_count':len(sensors),'interval_pairs':tested,
            'minimum_interval_separation':minimum}


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('n',type=int)
    parser.add_argument('--sensors',type=Path,help='JSON list of [x,y] sensors to check')
    args=parser.parse_args()
    sensors=({tuple(s)for s in json.loads(args.sensors.read_text())}
             if args.sensors else placement(args.n))
    print(json.dumps({'n':args.n,'sensors':sorted(sensors),**check(args.n,sensors)},indent=2))
