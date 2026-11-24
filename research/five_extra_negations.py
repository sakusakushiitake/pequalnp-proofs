"""Verify the coverage of the extra-negation searches and regenerate individual CNFs.

The first catalog excludes circuits with zero or one NOT. For each minimum-size
candidate with two or more NOT gates, five essential inputs require at least four
other gates. Thus sizes six through upper-1 suffice. Each record is either one
unsplit search or every canonical first gate. The record is a solver outcome;
--solve reproduces it, and --dimacs writes a CNF suitable for an LRAT solver.
"""
import argparse,json
from collections import defaultdict
from pathlib import Path
from five_input_catalog import DIRECTORY,verify_catalog
from five_input_exact import canonical,Solver

def verify_records(records):
    rows=verify_catalog()
    leaders={min(r['table'],r['dual']):len(r['plan']) for r in rows}
    expected={(f,k) for f,u in leaders.items() for k in range(6,u)}
    got=set()
    for r in records:
        f,k=r['table'],r['size'];assert (f,k) not in got
        assert r['unsatisfiable'] is True
        if r['first'] is not None:
            _,groups=canonical(int(f,16),k,not_limit=None,not_minimum=2)
            assert r['first']==list(range(len(groups[0])))
        got.add((f,k))
    assert got==expected and len(leaders)==95
    return len(rows),len(leaders),len(expected)

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--records',type=Path,default=DIRECTORY/'five_extra_negation_results.json')
    p.add_argument('--target',type=lambda s:int(s,16));p.add_argument('--size',type=int)
    p.add_argument('--first',type=int);p.add_argument('--dimacs',type=Path);p.add_argument('--solve',action='store_true')
    a=p.parse_args()
    if a.target is None:
        print('permutation classes, duality classes, size tests:',*verify_records(json.loads(a.records.read_text())))
    else:
        if a.size is None:p.error('--target requires --size')
        cnf,gates=canonical(a.target,a.size,a.first,not_limit=None,not_minimum=2)
        if a.dimacs:cnf.to_file(str(a.dimacs))
        if a.solve:
            with Solver(name='cadical195',bootstrap_with=cnf.clauses) as s:print('SAT' if s.solve() else 'UNSAT')
