#!/usr/bin/env python3
"""Check the published numerical rows and a high-precision direct-period case."""
import argparse
from decimal import Decimal as D
from fractions import Fraction as F
from math import lcm
from pathlib import Path
import subprocess
import test_native_detector as ref


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--bin',required=True)
    binary=str(Path(parser.parse_args().bin).resolve());checks=0
    def run(N,M,b=10):
        p=subprocess.run([binary,'native-refinement','mask-capture',str(N),str(M),str(b)],capture_output=True,text=True,check=True,timeout=30)
        assert 'not interval-certified' in p.stdout and 'no address truncation' in p.stdout
        return {key:D(value) for line in p.stdout.splitlines() if '=' in line and ' ' not in line for key,value in [line.split('=',1)]}
    for N,M,target in [(20,48,('77.5899','91.4437','95.0376')),(48,100,('39.0480','95.7508','96.0086')),(100,200,('64.4084','98.5642','98.6975'))]:
        got=run(N,M)
        for name,expected in zip(('masks','addresses','joint'),target):
            assert abs(100*got[name+'_fraction']-D(expected))<D('.000051'),(N,M,name,got)
            checks+=1
        assert 0<got['masks_capture']<=got['joint_capture']<=got['available_gain']*(1+D('1e-8'));checks+=1
    N,M,b=2,8,3;got=run(N,M,b);clocks=list(range(2,M+1));period=2*b*b*(b-1)
    G=[[ref.gram(j,k) for k in clocks] for j in clocks];means=[D(j).ln()/j for j in clocks]
    old=[row[:N-1] for row in G[:N-1]];p=ref.solve(old,means[:N-1]);q=ref.solve(G,means)
    sigma=lambda n:(-1)**((n//(b*b)+(n//b)%b+n%b)//(b-1))
    probes=[]
    for s in range(b-1):
        values=[]
        for j in clocks:
            length=lcm(period,j)
            values.append(sum((D((sigma(r+s+1)-sigma(r+s))//2)*D(r%j)/j*(ref.psi(F(r+1,length))-ref.psi(F(r,length)))/length for r in range(1,length+1)),D()))
        probes.append(values)
    for n in range(1,b):probes.append([ref.dec(F(n%j,j*n*(n+1))) for j in clocks])
    fine=[ref.solve(G,h) for h in probes];coarse=[ref.solve(old,h[:N-1]) for h in probes]
    response=[ref.dot(q,h)-ref.dot(p,h[:N-1]) for h in probes]
    K=[[ref.dot(h,f)-ref.dot(h[:N-1],c) for f,c in zip(fine,coarse)] for h in probes]
    for name,indices in [('masks',range(b-1)),('addresses',range(b-1,2*(b-1))),('joint',range(2*(b-1)))]:
        matrix=[[K[i][j] for j in indices] for i in indices];r=[response[i] for i in indices];capture=ref.dot(r,ref.solve(matrix,r))
        assert abs(got[name+'_capture']-capture)<D('2e-11'),(name,got[name+'_capture'],capture);checks+=1
    for args in [('1','4'),('4','4'),('2','201'),('2','8','11'),('2x','8')]:
        p=subprocess.run([binary,'native-refinement','mask-capture',*args],capture_output=True,text=True)
        assert p.returncode!=0 and not p.stdout;checks+=1
    print(f'PASS native directional controls: {checks} comparisons; all published table rows and independent 100-digit complete residue-period projections. Numerical calculations remain labeled numerical.')


if __name__=='__main__':main()
