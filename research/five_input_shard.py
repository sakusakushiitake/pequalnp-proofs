"""Sharded five-input one-NOT comparison, L-meta-1422.

Generate a DIMACS instance for size one below an explicit monotone upper
bound. A smaller output can be moved to the last wire by copying it. The
constant and copy gates include all cases of missing or repeated operands.
Install python-sat to generate instances outside this workspace.
"""
import argparse
from pathlib import Path
import sys

workspace_deps=Path(__file__).resolve().parent.parent/'.pnp'/'python'
if workspace_deps.is_dir():
    sys.path.insert(0,str(workspace_deps))
from pysat.card import CardEnc
from pysat.formula import CNF, IDPool

TABLES=(0xaaa8a880,0xe888a888,0xe888e880,0xe8a8a880,0xe8a8c880,
        0xe8a8e800,0xeaa8c080,0xeaaac000,0xeac8e000,0xaaa8a888)
UPPER=(8,6,8,9,8,7,7,4,7,6)


def one_hot(cnf,ids,choices):
    cnf.extend(CardEnc.equals(choices,1,vpool=ids).clauses)


def instance(target,size,not_limit=1):
    cnf,ids=CNF(),IDPool()
    rows=range(32)
    values=[[ids.id(('wire',j,x)) for x in rows] for j in range(5+size)]
    for x in rows:
        for j in range(5):
            v=values[j][x]; cnf.append([v if (x>>j)&1 else -v])
        output=values[-1][x];cnf.append([output if (target>>x)&1 else -output])
    nots=[]
    for w in range(5,5+size):
        ops={op:ids.id((op,w)) for op in ('and','or','not','zero','one')}
        one_hot(cnf,ids,list(ops.values()));nots.append(ops['not'])
        selectors=[[ids.id(('read',w,side,j)) for j in range(w)] for side in (0,1)]
        for switches in selectors:one_hot(cnf,ids,switches)
        # Only binary symmetric gates have their operands sorted. Negation
        # reads the left wire alone, and either constant ignores both.
        for j in range(1,w):
            for op in ('and','or'):
                cnf.append([-ops[op],-selectors[0][j],*selectors[1][j:]])
        for x in rows:
            a,b=[ids.id(('operand',w,side,x)) for side in (0,1)]
            for result,switches in zip((a,b),selectors):
                for j,switch in enumerate(switches):
                    v=values[j][x]
                    cnf.extend([[-switch,-result,v],[-switch,result,-v]])
            v=values[w][x]
            for op,rules in [('and',[[-v,a],[-v,b],[v,-a,-b]]),
                             ('or',[[v,-a],[v,-b],[-v,a,b]]),
                             ('not',[[v,a],[-v,-a]]),('zero',[[-v]]),('one',[[v]])]:
                cnf.extend([[-ops[op],*clause] for clause in rules])
    if not_limit is not None:
        cnf.extend(CardEnc.atmost(nots,not_limit,vpool=ids).clauses)
    return cnf


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('directory',type=Path)
    parser.add_argument('indices',nargs='*',type=int)
    args=parser.parse_args()
    args.directory.mkdir(exist_ok=True,parents=True)
    for i in args.indices or range(len(TABLES)):
        if i not in range(len(TABLES)):parser.error('index must be between 0 and 9')
        f=instance(TABLES[i],UPPER[i]-1)
        path=args.directory/f'{i}-{TABLES[i]:08x}-g{UPPER[i]-1}.cnf'
        f.to_file(str(path))
        print(path,f.nv,len(f.clauses))
