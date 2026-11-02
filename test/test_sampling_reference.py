"""Reproduce the high-resolution sampling table through the reusable C API.

Capacity is independently evaluated from the Jordan-totient identity with
50-digit Decimal arithmetic. The printed defect fixtures test manuscript
data reproduction to their six displayed decimals, not an asymptotic claim.
The sampled energy accumulator is exact; direct small-grid energy oracles
are in test_recent_paper_computations.py.
"""
from decimal import Decimal as D, localcontext
from fractions import Fraction
from pathlib import Path
import json
import subprocess

BIN=Path(__file__).resolve().parents[1]/'nfield'
BASES=(3,5,7,11,13,17,19,23,29,31,53,101,199,307,401,601,809,
       1009,1201,1601,2003,3001,4001,5003,7001,10007)
TABLE={31:'0.951176',101:'1.026972',199:'1.058311',401:'1.011478',809:'1.013187',
       1201:'0.992167',2003:'1.010416',3001:'1.008431',4001:'0.999951',
       5003:'1.002754',7001:'1.006215',10007:'1.008630'}
records=[]
with localcontext() as ctx:
    ctx.prec=50
    maximum=max(BASES)-1
    harmonic=[D(0)]*(maximum+1)
    jordan=[n*n for n in range(maximum+1)]
    for n in range(1,maximum+1):harmonic[n]=harmonic[n-1]+D(1)/n
    for p in range(2,maximum+1):
        if jordan[p]==p*p:
            for n in range(p,maximum+1,p):jordan[n]=jordan[n]//(p*p)*(p*p-1)
    for p in BASES:
        output=subprocess.run([str(BIN),'collision-sampling','sampled',str(p)],
                              text=True,capture_output=True,timeout=180,check=True).stdout
        row=dict(line.split('=',1) for line in output.splitlines())
        sample=Fraction(row['sampled']);sample=D(sample.numerator)/D(sample.denominator)
        cap=sum((D(jordan[d])*harmonic[(p-1)//d]**2/(3*d*d) for d in range(1,p)),D(0))
        defect=cap-sample
        assert abs(cap-D(row['capacity_numerical']))<D('5e-10'),(p,row,cap)
        assert abs(defect-D(row['defect_numerical']))<D('5e-10'),(p,row,defect)
        if p in TABLE:assert abs(defect-D(TABLE[p]))<=D('0.0000005'),(p,defect)
        records.append({'prime':p,'sampled':row['sampled'],'capacity':str(cap),'defect':str(defect)})
print(json.dumps({'passed':True,'capacity_checks':len(BASES),'printed_table_checks':len(TABLE),
                  'records':records},indent=2))
