#!/usr/bin/env python3
"""Independent finite prefix populations, interval costs and component matrices.

Forward word products do not use the implementation's golden-interval test.
Stopped costs are summed over open prefix intervals, including nonunits.
Matrix integrals use independent three-point polynomial quadrature; boundary
entries are also recovered by polarization of the existing scalar interface.
Shell inversion uses triangular elimination rather than Mobius inversion.
"""
import argparse
from fractions import Fraction as F
from math import gcd
from pathlib import Path
import subprocess
from test_field_observation import C,add,sub,scale,mul,sumc,zero,textlist,saw
from test_sampling_source import words

checks=0
def check(ok,label):
    global checks
    checks+=1
    assert ok,label
def conj(z):return z[0],-z[1]
def pair(a,b):return mul(conj(a),b)
def fields(line):return dict(part.split('=',1) for part in line.split() if '=' in part)

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--bin',required=True)
    binary=str(Path(parser.parse_args().bin).resolve())
    def run(family,*args,fail=False):
        p=subprocess.run([binary,family,*map(str,args)],capture_output=True,text=True,timeout=45)
        check((p.returncode!=0)==fail,(args,p.stdout[-1000:],p.stderr))
        if fail:check(not p.stdout,('rejected inputs emitted output',args));return
        return p.stdout
    def sample(*args,**kw):return run('collision-sampling',*args,**kw)
    def observe(*args,**kw):return run('field-observation',*args,**kw)
    def scalars(text):return {k:F(v) for line in text.splitlines() if '=' in line and ' ' not in line for k,v in [line.split('=',1)]}
    allwords=words(512)
    for first,last in [(2,512),(2,4),(8,8),(97,101),(512,512)]:
        output=sample('prefix-population',first,last);actual={};counts={}
        for line in output.splitlines():
            row=fields(line)
            if line.startswith('A='):
                A,B,C0,E,det,length=(int(row[k]) for k in ['A','B','C','E','determinant','length'])
                word=[tuple(map(int,x.split(':'))) for x in row['word'].split(',')]
                check((A,B) not in actual,'no repeated prefix')
                actual[A,B]=(C0,E,word)
                check(det==A*E-B*C0 and length==len(word)>=2,'prefix determinant and length')
            elif line.startswith('denominator='):counts[int(row['denominator'])]=row
            elif line.startswith('first='):total=int(row['total_population'])
        expected={key:value for key,value in allwords.items() if first<=key[0]<=last and len(value[2])>=2}
        check(actual==expected,'complete forward-generated population, both orientations')
        check(total==len(expected) and len(counts)==last-first+1,'population range totals')
        for A,row in counts.items():
            plus=sum(A*E-B*C0==1 for (a,B),(C0,E,_) in expected.items() if a==A)
            minus=sum(A*E-B*C0==-1 for (a,B),(C0,E,_) in expected.items() if a==A)
            check(int(row['positive_orientation'])==plus and int(row['negative_orientation'])==minus,'orientation totals')
    print('PASS complete prefix populations through denominator 512',flush=True)
    cases=[(k,H) for k in range(2,30) for H in range(1,k+1)]
    cases += [(43,1),(64,1),(97,2),(128,3),(256,7),(511,32),(512,1),(512,128),(512,512)]
    for k,H in cases:
        expected=[F(0) for _ in range(k)]
        # The theorem's extension is an interval sum, without coprimality
        # restrictions. This oracle never follows a nearest-remainder path.
        for (A,B),(C0,E,_) in allwords.items():
            if A*H>=k:continue
            det=A*E-B*C0
            for c in range(1,(k+1)//2):
                e=det*(A*c-C0*k);u=det*(E*k-B*c)
                if e>H and u>2*e:
                    expected[c]-=det*F(e*e+u*u+1-3*e*u,12*e*u)
        output=sample('stopped-cost',k,H);rows=[fields(line) for line in output.splitlines() if line.startswith('residue=')]
        check(len(rows)==k,'all residues, including zero')
        for c,row in enumerate(rows):
            check(int(row['residue'])==c and int(row['unit'])==(gcd(c,k)==1),'unit label')
            check(F(row['cost'])==expected[c],('open prefix interval cost',k,H,c))
            check(F(row['cyclic_jump'])==expected[c]-expected[c-1],'cyclic endpoints retained')
        got=scalars(output);tv=sum(abs(expected[c]-expected[c-1]) for c in range(k))
        check(got['cyclic_variation']==tv<=got['variation_bound']==8*F(k*k,H*H),'complete variation bound')
        check(got['variation_margin']==8*F(k*k,H*H)-tv,'exact variation allowance')
    print('PASS stopped-cost interval extension, nonunits and endpoint jumps',flush=True)

    def matrix_output(args):
        raw=observe(*args,'--matrix');matrices={}
        for line in raw.splitlines():
            if line.startswith('matrix='):
                row=fields(line);key=(int(row['row']),int(row['column']))
                entries=matrices.setdefault(row['matrix'],{});check(key not in entries,'unique matrix entry')
                entries[key]=tuple(map(F,row['value'].split(':')))
        totals=scalars(raw)
        n=int(totals['matrix_size'])
        for name,entries in matrices.items():
            check(set(entries)=={(i,j) for i in range(n) for j in range(n)},'complete matrix')
            check(all(entries[i,j]==conj(entries[j,i]) for i in range(n) for j in range(n)),'Hermitian symmetry')
            total=sumc(entries.values());scalar={'continuous':'continuous_energy','sampled':'sampled_energy'}.get(name,name)
            check(total==C(totals[scalar]),('all-ones coefficient reconstruction',name))
        return matrices

    def matrix_case(kind,q,theta,data,values,boundaries):
        n=len(values);args=[kind,q,theta,*map(textlist,data)]
        matrices=matrix_output(args)
        for i in range(n):
            for j in range(n):
                integral=zero
                for a,b in zip(boundaries,boundaries[1:]):
                    width=b-a
                    samples=[pair(values[i](a+width*t),values[j](a+width*t)) for t in [F(1,4),F(1,2),F(3,4)]]
                    integral=add(integral,scale(add(sub(scale(samples[0],2),samples[1]),scale(samples[2],2)),width/3))
                sampled=scale(sumc(pair(values[i]((F(a)+theta)/q),values[j]((F(a)+theta)/q)) for a in range(q)),F(1,q))
                check(matrices['continuous'][i,j]==integral,'independent component quadrature')
                check(matrices['sampled'][i,j]==sampled,'literal component grid')
                check(matrices['defect'][i,j]==sub(integral,sampled),'signed mixed defect')
        # Polarize independently evaluated scalar fields, including complex
        # recombination of the actual pulse endpoint readings.
        def evaluate(coefficients):
            changed=[list(x) for x in data]
            for index in ([2,3,4] if kind=='pulses' else [2]):
                changed[index]=[mul(c,v) for c,v in zip(coefficients,changed[index])]
            return scalars(observe(kind,q,theta,*map(textlist,changed)))
        unit=[]
        for i in range(n):unit.append(evaluate([C(int(j==i)) for j in range(n)]))
        for i in range(n):
            for j in range(i+1,n):
                z=[zero]*n;z[i]=C(1);z[j]=C(1);real=evaluate(z)
                z[j]=C(0,1);imag=evaluate(z)
                for channel in ['point_correction','value_jump','derivative_jump']:
                    want=C((real[channel]-unit[i][channel]-unit[j][channel])/2,-(imag[channel]-unit[i][channel]-unit[j][channel])/2)
                    check(matrices[channel][i,j]==want,('boundary polarization',kind,channel))
        return matrices

    clock_sets=[([1,1],[F(0),F(0)],[C(1),C(-1)]),([2,2,3],[F(1,3),F(1,3),F(1,2)],[C(2,1),C(-1,2),C(F(1,3),-1)])]
    for frequencies,phases,amps in clock_sets:
        values=[lambda x,r=r,p=p,a=a:scale(a,2*saw(r*x+p)) for r,p,a in zip(frequencies,phases,amps)]
        boundaries=sorted({F(0),F(1)}|{((F(j)-p)/r)%1 for r,p in zip(frequencies,phases) for j in range(r)})
        for q,theta in [(1,F(0)),(4,F(0)),(7,F(2,7)),(11,F(1,2))]:matrix_case('clocks',q,theta,[frequencies,phases,amps],values,boundaries)
    for left,right,amps,lv,rv in [([F(0),F(1,2)],[F(1,2),F(1)],[C(1),C(3)],[C(1),C(1)],[C(1),C(1)]),([F(1,4),F(1,2)],[F(3,4),F(1)],[C(1,2),C(-1,1)],[C(0),C(1)],[C(2,-1),C(0)]),([F(0)],[F(1)],[C(2,3)],[C(1)],[C(1)])]:
        values=[lambda x,a=a,b=b,z=z,u=u,v=v:u if x==a else v if x==b or (x==0 and b==1) else z if a<x<b else zero for a,b,z,u,v in zip(left,right,amps,lv,rv)]
        for q,theta in [(1,F(0)),(4,F(0)),(7,F(1,2))]:matrix_case('pulses',q,theta,[left,right,amps,lv,rv],values,sorted(set(left+right+[F(0),F(1)])))
    roots=[C(1),C(0,1),C(-1),C(0,-1)]
    for frequencies in [[1,-1],[0,4,-4],[10000,-10000,0]]:
        amps=[C(1,2),C(-1,1),C(3)][:len(frequencies)]
        for q,theta in [(1,F(0)),(2,F(0)),(4,F(0)),(2,F(1,2))]:
            m=matrix_output(['harmonics',q,theta,textlist(frequencies),textlist(amps)])
            for i,r in enumerate(frequencies):
                for j,s in enumerate(frequencies):
                    expected=scale(sumc(mul(pair(amps[i],amps[j]),roots[int(4*(s-r)*(F(a)+theta)/q)%4]) for a in range(q)),F(1,q))
                    check(m['sampled'][i,j]==expected,'literal exact fourth-root sampling')
                    check(m['continuous'][i,j]==(pair(amps[i],amps[j]) if r==s else zero),'orthogonal Fourier integral')
    # Domain boundaries: all sixteen components and the maximum grid size.
    matrix_output(['clocks',10000,0,textlist([1]*16),textlist([0]*16),textlist([C(i-8,i%3) for i in range(16)])])
    matrix_output(['clocks',17,0,'120,120,120,120,32','0,0,0,0,0','1,2,3,4,5'])
    print('PASS complete complex clock, pulse and harmonic matrices',flush=True)

    for prefix in [[F(0)],[F(1),F(4),F(8)],[F((-1)**i*(i+1),i+2) for i in range(31)],[F((i*17)%23-11,i%7+1) for i in range(256)]]:
        recovered=[]
        for n,value in enumerate(prefix,1):recovered.append(value-sum((n//m*recovered[m-1] for m in range(1,n)),F(0)))
        reverse=observe('shells',textlist(prefix),'--from-prefixes');forward=observe('shells',textlist(recovered))
        check(reverse==forward,'reverse and forward modes return identical reconstruction')
        for row in [fields(line) for line in reverse.splitlines() if line.startswith('cutoff=')]:
            n=int(row['cutoff']);check(F(row['primitive_shell'])==recovered[n-1] and F(row['square_prefix'])==prefix[n-1],'triangular shell elimination')
    for args in [('prefix-population',1,8),('prefix-population',8,7),('prefix-population',2,513),('stopped-cost',0,1),('stopped-cost',513,1),('stopped-cost',5,0),('stopped-cost',5,6)]:sample(*args,fail=True)
    for args in [('shells','1:2,3','--from-prefixes'),('shells',textlist([0]*257),'--from-prefixes'),('shells','1,2','--matrix'),('clocks',0,0,1,0,1,'--matrix'),('clocks',4,0,'120,120,120,120,120','0,0,0,0,0','1,1,1,1,1','--matrix'),('clocks',4,0,1,0,1,'--matrix','--matrix'),('pulses',4,0,0,1,1,0,1,'--matrix'),('harmonics',4,'1/3',1,1,'--matrix')]:observe(*args,fail=True)
    check('prefix-population' in subprocess.check_output([binary,'__complete','collision-sampling'],text=True),'prefix discovery')
    check('--from-prefixes' in subprocess.check_output([binary,'__complete','field-observation'],text=True),'inverse discovery')
    print(f'PASS published command gaps: {checks} independent checks; full populations, all-residue costs, component matrices and reverse shell inputs.')

if __name__=='__main__':main()
