from itertools import permutations
import json
from pathlib import Path
import numpy as np
from hensel_planes import rref,cells,index

w=Path(__file__).resolve().parent
def orbits():
    planes=json.loads((w/'symmetric-hensel-three.json').read_bytes())
    basis=[np.array(q['basis'],dtype=np.int64) for q in planes]
    ids={a.tobytes():i for i,a in enumerate(basis)}
    orbs=[]
    done=set()
    for i,A in enumerate(basis):
        if i in done: continue
        a=np.column_stack((A,-2*A[:,:6].sum(axis=1)-A[:,6:].sum(axis=1)))%3
        orb=set()
        for p in permutations(range(4)):
            ii=[index[tuple(sorted((p[x],p[y])))] for x,y in cells[:-1]]
            U,ps=rref(a[:,ii])
            orb.add(ids[U.tobytes()])
        assert not orb&done
        orbs.append(sorted(orb))
        done|=orb
    return orbs
if __name__=='__main__':
    for a in orbits():print(a)
