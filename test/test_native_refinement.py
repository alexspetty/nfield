#!/usr/bin/env python3
"""Contracts and archival comparisons. Mathematics is evaluated in C/MPFR."""
import json
import subprocess
import tempfile
from decimal import Decimal, getcontext
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BIN = ROOT / "nfield"
FIXTURE = ROOT / "test/fixtures/native_refinement_4_6.json"
getcontext().prec=80

def run(*args, ok=True):
    p = subprocess.run([str(BIN), *map(str,args)], capture_output=True, text=True, timeout=180)
    assert (p.returncode == 0) == ok, (args, p.returncode, p.stdout, p.stderr)
    return p

def overlap(a,b):
    assert Decimal(a['lo']) <= Decimal(b['hi']) and Decimal(b['lo']) <= Decimal(a['hi']), (a,b)

def trace(first,last):
    p=run('native-refinement','trace',first,last,'--json')
    d=json.loads(p.stdout)
    assert d['schema']=='nfield.native-refinement.v1' and d['status']=='PASS'
    assert d['first']==first and d['last']==last and d['failures']==0 and d['checks']>100
    assert d['observation_truncation'] is False and d['uniform_lower_bound_proved'] is False
    assert d['complete_period_audit'] is (last<=8)
    def visit(x):
        if isinstance(x,dict):
            if set(x)=={'lo','hi'}:
                lo,hi=Decimal(x['lo']),Decimal(x['hi'])
                assert lo.is_finite() and hi.is_finite() and lo<=hi and hi-lo<Decimal('1e-38')
            else:
                for v in x.values(): visit(v)
        elif isinstance(x,list):
            for v in x: visit(v)
    visit(d)
    return d,p.stdout

small,_=trace(1,2)
assert small['period']==2
overlap(small['frames'][0]['D'],{'lo':'1','hi':'1'})
archived=json.loads(FIXTURE.read_text())
six,six_text=trace(4,6)
for old in archived['frames']:
    new=six['frames'][old['N']-1]
    for key in ('D','capacity'): overlap(old[key],new[key])
last=six['frames'][-1]
for oldkey,newkey in (
    ('signed_response_psi','block_response_psi'),('complete_cost_psi','block_cost_psi'),
    ('certificate_L','certificate_L'),('actual_raw_gain','block_gain'),
    ('capture_fraction','capture_fraction'),('invisible_gain','invisible_gain'),
    ('L_over_D4_squared','L_over_D_first_squared'),('L_over_D4_D6','L_over_D_first_D_last')):
    overlap(archived['origin_certificate'][oldkey],last[newkey])
for old in archived['ordered_raw_modes']:
    new=six['frames'][old['admitted_clock']-1]
    for oldkey,newkey in (('gain_coordinate','gamma'),('origin_coordinate_psi','omega_psi'),
                          ('signed_origin_contribution_psi','signed_origin_contribution_psi'),
                          ('projected_origin_norm_psi','step_origin_cost_psi')):
        overlap(old[oldkey],new[newkey])
for row in six['conditioned_gram']:
    key=f"H{min(row['j'],row['k'])}{max(row['j'],row['k'])}"
    overlap(archived['old_conditioned_block'][key],row['value'])
print('PASS: 26 archived 4-to-6 interval comparisons')

eight,eight_text=trace(4,8)
all_frames,_=trace(1,8)
assert eight['period']==840
for x,y in zip(eight['frames'],all_frames['frames']):
    for key in ('D','capacity'): overlap(x[key],y[key])
for j in (5,6):
    for key in ('block_gain','block_response_psi','block_cost_psi','certificate_L','capture_fraction'):
        overlap(six['frames'][j-1][key],eight['frames'][j-1][key])
assert eight['frames'][6]['raw_reset_pulses']==[7,21]
assert eight['frames'][7]['raw_reset_pulses']==[]
assert eight['frames'][6]['raw_origin_eta']=='1609/45045'
assert eight['frames'][7]['raw_origin_eta']=='-131/17160'
assert Decimal(eight['frames'][6]['signed_origin_contribution_psi']['lo'])>0
assert Decimal(eight['frames'][7]['signed_origin_contribution_psi']['hi'])<0
print('PASS: frame-independent optimizers, old block replay and exact clock 7/8 resets')

collision=run('native-refinement','collision4','--json')
collision_data=json.loads(collision.stdout)
assert collision_data['schema']=='nfield.native-refinement.collision4-calibration.v1'
assert collision_data['status']=='PASS' and collision_data['checks']>27000
assert collision_data['extension']=='centered base-2 lag-one table; zero off units'
for key in ('native_mean','native_norm_squared','shell_projection_norm_squared','certificate_J','capture_fraction','normalized_certificate'):
    assert Decimal(collision_data[key]['lo'])>0, (key,collision_data[key])
assert Decimal(collision_data['signed_response']['hi'])<0
assert Decimal(collision_data['capture_fraction']['hi'])<Decimal('0.001')
response_lo=sum((Decimal(row['signed_contribution']['lo']) for row in collision_data['innovations']),Decimal(0))
response_hi=sum((Decimal(row['signed_contribution']['hi']) for row in collision_data['innovations']),Decimal(0))
assert response_lo<=Decimal(collision_data['signed_response']['hi'])
assert Decimal(collision_data['signed_response']['lo'])<=response_hi
assert 'finite calibration' in run('native-refinement','collision4').stdout
run('native-refinement','collision4','--output','x',ok=False)
run('native-refinement','collision4','--json','--json',ok=False)
print('PASS: collision4 extension, complete-weight calibration and innovation reconstruction')

families=run('native-refinement','collision-families','--json')
family_data=json.loads(families.stdout)
assert family_data['schema']=='nfield.native-refinement.collision-families.v1'
assert family_data['status']=='PASS' and family_data['checks']>29000
by_modulus={row['modulus']:row for row in family_data['families']}
assert set(by_modulus)=={4,9,25}
assert (by_modulus[4]['finite_orbit_rank'],by_modulus[4]['projected_shell_rank'])==(1,1)
assert (by_modulus[9]['finite_orbit_rank'],by_modulus[9]['projected_shell_rank'])==(2,2)
assert (by_modulus[25]['finite_orbit_rank'],by_modulus[25]['projected_shell_rank'])==(8,4)
assert Decimal('.61')<Decimal(by_modulus[9]['capture_fraction']['lo'])<Decimal('.63')
assert Decimal(by_modulus[25]['capture_fraction']['lo'])>Decimal('.999999999999999999999999999999999999')
assert len(by_modulus[4]['observations'])==2
assert len(by_modulus[9]['observations'])==6
assert len(by_modulus[25]['observations'])==20
assert len(by_modulus[25]['observation_gram'])==210
assert [row['projected_rank'] for row in by_modulus[4]['prefixes']]==[1,1,1,1]
assert [row['projected_rank'] for row in by_modulus[9]['prefixes']]==[1,2,2,2]
assert [row['projected_rank'] for row in by_modulus[25]['prefixes']]==[1,2,3,4]
assert Decimal(by_modulus[9]['prefixes'][1]['capture_fraction']['lo'])>Decimal('.999999999999999999999999999999999999')
assert Decimal('.67')<Decimal(by_modulus[9]['prefixes'][2]['capture_fraction']['lo'])<Decimal('.69')
assert Decimal('.61')<Decimal(by_modulus[9]['prefixes'][3]['capture_fraction']['lo'])<Decimal('.63')
for row in by_modulus[25]['prefixes']:
    assert Decimal(row['capture_fraction']['lo'])>Decimal('.999999999999999999999999999999999999')
assert family_data['combined']['selected_observations']==[
    {'base':2,'multiplier':1},{'base':3,'multiplier':1},
    {'base':3,'multiplier':2},{'base':5,'multiplier':1}]
tower=family_data['profinite_tower']
assert tower['quotients']==[1,4,36,900] and tower['haar_cross_layer_orthogonal_exact'] is True
assert tower['native_union_ranks']==[1,3,4] and tower['native_rank_increments']==[1,2,1]
assert Decimal('.65')<Decimal(tower['native_cross_layer_overlap'][0]['hilbert_schmidt_squared']['lo'])<Decimal('.66')
assert Decimal(tower['q4_q9_interaction_surplus']['lo'])>Decimal('.015')
assert 'full-shell reconstruction is not a lower bound' in run('native-refinement','collision-families').stdout
run('native-refinement','collision-families','--output','x',ok=False)
run('native-refinement','collision-families','--json','--json',ok=False)
print('PASS: translated q=4,9,25 ranks, prefix losses, interaction Grams and collective capture')

families16=json.loads(run('native-refinement','collision-families','8','16','--json').stdout)
assert families16['first']==8 and families16['last']==16
assert families16['period']==720720 and families16['complete_period_audit'] is False
by_modulus16={row['modulus']:row for row in families16['families']}
assert by_modulus16[9]['projected_shell_rank']==2 and by_modulus16[9]['projected_rank_exact'] is True
assert Decimal('.10')<Decimal(by_modulus16[9]['capture_fraction']['lo'])<Decimal('.11')
assert by_modulus16[25]['finite_orbit_rank']==8
assert by_modulus16[25]['projected_shell_rank']==8 and by_modulus16[25]['projected_rank_exact'] is True
assert [row['projected_rank'] for row in by_modulus16[25]['prefixes']]==list(range(1,9))
assert all(row['projected_rank_exact'] is True for row in by_modulus16[25]['prefixes'])
assert all(Decimal(row['capture_fraction']['lo'])>Decimal('.99999999999999999999999999999999999') for row in by_modulus16[25]['prefixes'])
assert families16['combined']['projected_shell_rank']==8 and families16['combined']['projected_rank_exact'] is True
assert families16['profinite_tower']['native_union_ranks']==[1,3,8]
assert Decimal(families16['profinite_tower']['q4_q9_interaction_surplus']['hi'])<0
print('PASS: q=25 exhausts its exact rank budget one direction at a time on 8-to-16')

tower16=json.loads(run('native-refinement','collision-families','4','16','--json').stdout)
by_modulus_tower={row['modulus']:row for row in tower16['families']}
assert set(by_modulus_tower)=={4,9,25,49}
assert tower16['combined']['finite_tower_rank']==11
assert tower16['combined']['projected_shell_rank']==11 and tower16['combined']['projected_rank_exact'] is True
assert tower16['combined']['blind_codimension']==1
assert Decimal('.988')<Decimal(tower16['combined']['capture_fraction']['lo'])<Decimal('.989')
assert Decimal(tower16['combined']['missed_gain']['lo'])>Decimal('.00055')
assert len(tower16['combined']['blind_direction'])==12
q49=by_modulus_tower[49]
assert q49['finite_orbit_rank']==18 and q49['projected_shell_rank']==12 and q49['projected_rank_exact'] is True
assert [row['projected_rank'] for row in q49['prefixes']]==list(range(1,13))
extension=tower16['extension_49']
assert extension['quotient']==44100 and extension['rank_increment']==1 and extension['extended_tower_rank']==12
assert Decimal(extension['prior_blind_detection_fraction']['lo'])>Decimal('.999999999999999999999999999999999')
assert Decimal(extension['capture_fraction']['lo'])>Decimal('.999999999999999999999999999999999')
print('PASS: CRT tower exhausts rank 11 and q49 resolves the certified blind direction')

sixteen,_=trace(8,16)
assert sixteen['period']==720720 and sixteen['complete_period_audit'] is False
last16=sixteen['frames'][15]
assert Decimal(last16['block_gain']['lo'])>0
assert Decimal('.26')<Decimal(last16['capture_fraction']['lo'])<Decimal('.27')
assert Decimal(last16['certificate_L']['lo'])>Decimal('.0016')
print('PASS: fixed-origin 8-to-16 block and entrywise complete-weight extension')

driver=subprocess.run([str(ROOT/'test/native_refinement_runner')],check=True,capture_output=True,text=True,timeout=15)
assert driver.stdout==six_text
assert 'native-refinement' in run('commands').stdout
assert 'native-refinement' in run('__complete').stdout
completion=run('__complete','native-refinement').stdout
assert 'trace' in completion and 'collision-families' in completion
assert 'complete infinite native norm' in run('help','native-refinement').stdout
assert 'PASS' in run('verify','native-refinement').stdout
for args in [('trace','0','8'),('trace','4','17'),('trace','8','4'),('trace','4','4'),
             ('trace','4x','8'),('trace','4','8','--oops'),('trace','4','8','--output'),
             ('trace','4','8','--json','--json'),('trace','4','8','--time')]:
    run('native-refinement',*args,ok=False)
with tempfile.TemporaryDirectory() as directory:
    path=Path(directory)/'results.json'
    run('native-refinement','trace','4','8','--output',path)
    assert path.read_text()==eight_text
    before=path.read_bytes()
    run('native-refinement','trace','1','2','--output',path,ok=False)
    assert path.read_bytes()==before
    missing=Path(directory)/'missing/results.json'
    run('native-refinement','trace','1','2','--output',missing,ok=False)
print('PASS: library/CLI equality, discovery, invalid input, exclusive output and deterministic replay')
