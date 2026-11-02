#!/usr/bin/env python3
"""Independent rational oracle: divisor-budget weights and Ramanujan row steps.

The oracle evaluates every residue directly. The C implementation uses
primitive harmonic weights, signed Mobius rows and an integer reset recurrence.
These finite checks validate interval calculations; the Lean enclosure proofs
justify their relationship to the infinite quantities.
"""
import argparse
from fractions import Fraction as F
from functools import lru_cache
from math import gcd, lcm
from pathlib import Path
import subprocess


@lru_cache(None)
def divisors(n):
    return [d for d in range(1,n+1) if n%d==0]


@lru_cache(None)
def mu(n):
    primes=[p for p in range(2,n+1) if n%p==0 and all(p%d for d in range(2,p))]
    return 0 if any(n%(p*p)==0 for p in primes) else (-1)**len(primes)


@lru_cache(None)
def phi(n):
    return sum(gcd(a,n)==1 for a in range(1,n+1))


@lru_cache(None)
def weights(N):
    w=[F(0)]*(N+1)
    harmonic=F(0)
    for n in range(2,N+1):
        harmonic+=F(1,n-1)
        # Invert n*H_(n-1)=sum_(d|n) d^3*w_d, independently of coprime sums.
        w[n]=(n*harmonic-sum(d**3*w[d] for d in divisors(n) if d<n))/n**3
    return tuple(w)


@lru_cache(None)
def rows(q):
    values=[F(-phi(q),2)]
    for a in range(1,q):
        r=q//gcd(q,a)
        ramanujan=F(mu(r)*phi(q),phi(r))
        values.append(values[-1]-ramanujan)
    return tuple(values)


@lru_cache(None)
def table(Q,M):
    w=weights(max(Q,M)); tail=1-sum(w[2:M+1])
    eta={q:sum(w[k] for k in range(q,M+1,q)) for q in range(2,Q+1)}
    blo={}; bhi={}
    for d in range(2,Q+1):
        signs=[mu(j) for j in range(1,Q//d+1)]
        center=sum(mu(j)*eta[d*j] for j in range(1,Q//d+1))
        blo[d]=max(w[d]/2,center-signs.count(-1)*tail)
        bhi[d]=center+signs.count(1)*tail
    return w,tail,eta,blo,bhi


def value_reference(Q,a,M):
    w,tail,eta,blo,bhi=table(Q,M)
    # Regroup retained periods first, rather than summing C's amplitude array.
    center=sum(w[k]*sum(rows(q)[a%q] for q in divisors(k) if 2<=q<=Q)
               for k in range(2,M+1))*F(2,3)
    negative=sum(min(F(0),rows(q)[a%q]) for q in range(2,Q+1))
    positive=sum(max(F(0),rows(q)[a%q]) for q in range(2,Q+1))
    v=sum(w[k]*sum(phi(q) for q in divisors(k) if 2<=q<=Q) for k in range(2,M+1))/3
    L=lcm(*range(1,Q+1))
    return dict(conductor_cutoff=Q,period_cutoff=M,period=L,residue=a%L,
                value_lower=center+F(2,3)*tail*negative,
                value_upper=center+F(2,3)*tail*positive,
                endpoint_lower=v,endpoint_upper=v+tail*sum(phi(q) for q in range(2,Q+1))/3,
                gap_lower=F(2,3)*sum(blo[d]*(a%d) for d in blo),
                gap_upper=F(2,3)*sum(bhi[d]*(a%d) for d in bhi),
                unique_minimum_residue=0,unique_maximum_residue=L-1)


@lru_cache(None)
def extrema_reference(Q,M):
    _,_,_,blo,bhi=table(Q,M); L=lcm(*range(1,Q+1))
    den=lcm(*(x.denominator for x in [*blo.values(),*bhi.values()]))
    il={d:int(v*den) for d,v in blo.items()}; ih={d:int(v*den) for d,v in bhi.items()}
    # Direct dot products at all residues, independent of C's reset recurrence.
    lower=[sum(v*(a%d) for d,v in il.items()) for a in range(1,L-1)]
    upper=[sum(v*(a%d) for d,v in ih.items()) for a in range(1,L-1)]
    ml=min(lower); mh=min(upper); witness=upper.index(mh)+1
    candidates={a:(F(2*lower[a-1],3*den),F(2*upper[a-1],3*den))
                for a in range(1,L-1) if lower[a-1]<=mh}
    out=dict(conductor_cutoff=Q,period_cutoff=M,period=L,
             restricted_gap_lower=F(2*ml,3*den),restricted_gap_upper=F(2*mh,3*den),
             upper_bound_witness=witness,possible_minimizer_count=len(candidates))
    if len(candidates)==1: out['certified_unique_minimizer']=witness
    else: out['minimizer_status']='overlapping_intervals'
    return out,candidates


def parse(text):
    out={}; candidates={}
    for line in text.splitlines():
        if line.startswith('possible_minimizer='):
            fields=dict(x.split('=',1) for x in line.split())
            a=int(fields['possible_minimizer']); assert a not in candidates
            candidates[a]=(F(fields['gap_lower']),F(fields['gap_upper']))
        elif '=' in line:
            key,value=line.split('=',1)
            try: value=F(value)
            except ValueError: pass
            assert key not in out,(key,text)
            out[key]=value
    return out,candidates


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--bin',default='./nfield'); parser.add_argument('--driver',required=True)
    parser.add_argument('--driver-only',action='store_true')
    args=parser.parse_args(); driver=str(Path(args.driver).resolve()); binary=str(Path(args.bin).resolve())
    commands=[]; expected=[]; checks=0
    def add(command,result,candidates=None):
        commands.append(command); expected.append((dict(result,exit=0),candidates or {}))
    # Include every residue for small Q, both endpoint classes, negative and huge addresses,
    # cutoffs below/above Q, prime squares and the implementation boundary.
    for Q in [2,3,4,5,6,7,8,9,10,11,12,16,25,49,120,239,240]:
        L=lcm(*range(1,Q+1))
        addresses=sorted(set([0,1,-1,-2,L-1,L,L+1,-L-1,10**90+7,-10**90-7]+list(range(min(L,13)))))
        for M in [2,7,31,240]:
            for a in addresses: add(f'conductor-full {Q} {a} {M}',value_reference(Q,a,M))
            _,_,_,lo,hi=table(Q,M)
            for d in range(2,Q+1):
                add(f'conductor-beta {d} {Q} {M}',dict(row=d,conductor_cutoff=Q,period_cutoff=M,
                                                    beta_lower=lo[d],beta_upper=hi[d]))
                assert 0<lo[d]<=hi[d]; checks+=2
    for Q in [*range(3,40),49,120,239,240]:
        L=lcm(*range(1,Q+1))
        for p in range(Q//2+1,Q+1):
            if phi(p)!=p-1: continue
            a=(L//p)*pow(L//p,-1,p)
            assert 0<a<L-1 and a%p==1 and all(a%d==0 for d in range(1,Q+1) if d!=p)
            checks+=3
            add(f'conductor-prime {Q} {p}',dict(conductor_cutoff=Q,prime=p,period=L,
                                              candidate_residue=a,candidate_gap='2*eta_prime/3'))
    for Q in range(3,13):
        for M in [2,7,31,240]:
            out,candidates=extrema_reference(Q,M)
            add(f'conductor-extrema {Q} {M}',out)
            if Q<=8: add(f'conductor-minimizers {Q} {M}',out,candidates)
            assert out['restricted_gap_lower']>0; checks+=1
    raw=subprocess.run([driver,'--stream'],input='\n'.join(commands)+'\n',text=True,capture_output=True,check=True)
    assert not raw.stderr,raw.stderr
    pieces=raw.stdout.split('BEGIN\n')[1:]; assert len(pieces)==len(expected)
    for command,piece,(want,candidates) in zip(commands,pieces,expected):
        assert piece.endswith('END\n'),piece[-80:]
        got,actual_candidates=parse(piece[:-4])
        assert got==want,(command,got,want)
        assert actual_candidates==candidates,(command,actual_candidates,candidates)
        checks+=len(want)+2*len(candidates)
    selftest=subprocess.run([driver,'--self-test'],capture_output=True,text=True,check=True)
    assert not selftest.stderr,selftest.stderr
    api_checks=int(selftest.stdout.strip().split('=')[1]); checks+=api_checks
    cli_checks=0
    if not args.driver_only:
        for action in ['conductor-full 12 -123456789012345678901 240','conductor-beta 4 12 31',
                       'conductor-prime 12 11','conductor-extrema 7 240','conductor-minimizers 4 7']:
            result=subprocess.run([binary,'weighted-remainder-state',*action.split()],capture_output=True,text=True,check=True)
            assert not result.stderr
            reference=subprocess.run([driver,'--stream'],input=action+'\n',capture_output=True,text=True,check=True)
            want,poss=parse(reference.stdout); want.pop('exit')
            assert parse(result.stdout)==(want,poss); cli_checks+=1
        invalid=['conductor-full 1 0 31','conductor-full 241 0 31','conductor-full 7 1x 31',
                 'conductor-full 7 --1 31','conductor-full 7 0 241','conductor-full 7 0 31 extra',
                 'conductor-beta 1 7 31','conductor-beta 8 7 31','conductor-beta -2 7 31',
                 'conductor-prime 7 4','conductor-prime 7 3','conductor-prime 2 2',
                 'conductor-extrema 13 31','conductor-extrema 2 31','conductor-extrema 7 1',
                 'conductor-minimizers 13 31','conductor-minimizers 7 31 extra']
        for action in invalid:
            result=subprocess.run([binary,'weighted-remainder-state',*action.split()],capture_output=True,text=True)
            assert result.returncode and not result.stdout,(action,result.stdout)
            cli_checks+=1
        for address in ['+123','-000123','000123']:
            result=subprocess.run([binary,'weighted-remainder-state','conductor-full','7',address,'31'],capture_output=True,text=True,check=True)
            assert parse(result.stdout)==(value_reference(7,int(address),31),{});cli_checks+=1
    checks+=cli_checks
    print(f'conductor_checks={checks}; queries={len(commands)}; api_edges={api_checks}; cli_cases={cli_checks}; PASS')


if __name__=='__main__': main()
