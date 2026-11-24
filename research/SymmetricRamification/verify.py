"""Verify the ramification-index-three obstruction; see README.md."""
import argparse
from collections import Counter
import json
from pathlib import Path
import shutil
import subprocess
import sys
from tempfile import TemporaryDirectory

MODULES=('symmetric_three','hensel_planes','three_orbits','ramified_three',
         'cubic_jets','quartic_jet','cubic_series')

def generate(root):
    root.mkdir(exist_ok=True,parents=True)
    source=Path(__file__).resolve().parent
    for name in MODULES:
        shutil.copyfile(source/(name+'.py'),root/(name+'.py'))
    for name in ('hensel_planes','ramified_three','cubic_jets','quartic_jet','cubic_series'):
        subprocess.run([sys.executable,str(root/(name+'.py'))],check=True)
    orbit=subprocess.run([sys.executable,'-c','import json; from three_orbits import orbits; print(json.dumps(orbits()))'],
                         cwd=root,check=True,text=True,capture_output=True)
    (root/'orbits.json').write_text(orbit.stdout,encoding='utf-8')

def verify(root,msolve):
    planes=json.loads((root/'symmetric-hensel-three.json').read_text())
    assert len(planes)==32 and all(not q['lift'] for q in planes)
    assert Counter(q['tangent'] for q in planes)=={4:12,6:16,9:4}
    orbits=json.loads((root/'orbits.json').read_text())
    assert [a[0] for a in orbits]==[0,1,5,18]
    assert sorted(i for a in orbits for i in a)==list(range(32))
    assert list(map(len,orbits))==[4,12,4,12]
    with TemporaryDirectory() as tmp:
        scratch=Path(tmp)
        def solve(data):
            path=scratch/'test.in'
            out=scratch/'test.out'
            if out.exists():out.unlink()
            path.write_text(data,encoding='ascii')
            subprocess.run([msolve,'-f',str(path),'-o',str(out),'-t','1','-l','2'],check=True,capture_output=True)
            result=out.read_text().strip()
            assert result
            return result
        def empty(data):
            assert solve(data)=='[-1]:'
        empty('x\n3\nx,x-1\n')
        assert solve('x\n3\nx^2+1\n')!='[-1]:'
        def force_zero(data,expression):
            names,p,eq=data.strip().split('\n',2)
            pieces=expression.replace('-','+-').split('+')
            product='+'.join(('-' if part.startswith('-') else '')+'inverse'+
                             ('' if part.lstrip('-')=='1' else '*'+part.lstrip('-')) for part in pieces if part)
            empty(names+',inverse\n'+p+'\n'+eq+',\n'+product.replace('+-','-')+'-1\n')
        for i in range(32):
            empty((root/'ramified-two/3'/f'{i:02d}.in').read_text())
        print('All 32 quadratic obstruction systems are empty.')
        for i in (0,1,18):
            empty((root/'ramified-cubic/3'/f'{i:02d}.in').read_text())
        cubic=(root/'ramified-cubic/3/05.in').read_text()
        for relation in ['s0','s1','s2','s4','s3+s5-1']:force_zero(cubic,relation)
        quartic=(root/'ramified-quartic/3/05.in').read_text()
        for relation in ['t2','t4','u']:force_zero(quartic,relation)
        fifth=(root/'ramified-quintic/3/05.in').read_text()
        empty(fifth)
        assert {'t0','t0^2+1'}<=set(q.strip().rstrip(',') for q in fifth.splitlines()[2:])
        print('All four S4 orbits are excluded through ramification index three.')

if __name__=='__main__':
    ap=argparse.ArgumentParser()
    mode=ap.add_mutually_exclusive_group()
    mode.add_argument('--generate',type=Path)
    mode.add_argument('--check',type=Path)
    ap.add_argument('--msolve',default='msolve')
    args=ap.parse_args()
    if args.generate:generate(args.generate.resolve())
    elif args.check:verify(args.check.resolve(),args.msolve)
    else:
        with TemporaryDirectory() as tmp:
            root=Path(tmp)
            generate(root)
            verify(root,args.msolve)
