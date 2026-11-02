"""Check the new mathematical readouts through the public JSON/TCP dispatcher.

The mathematics has independent oracles in test_recent_paper_computations.py.
Responses must preserve the complete CLI output, including diagnostics for
invalid inputs. The existing daemon returns output only, not an exit-code
field. Only an ephemeral loopback daemon is used.
"""
import json
from pathlib import Path
import shlex
import socket
import subprocess
import tempfile
import time

BIN = str(Path(__file__).resolve().parents[1] / 'nfield')
COMMANDS = [
    ('collision-sampling prefix-population 5 12', True),
    ('collision-sampling stopped-cost 64 2', True),
    ('field-observation clocks 4 0 1,2 0,0 1,-1 --matrix', True),
    ('field-observation pulses 4 0 0,1/2 1/2,1 1,3 1,1 1,1 --matrix', True),
    ('field-observation harmonics 4 0 1,-3 1,0:1 --matrix', True),
    ('field-observation shells 1,4,8 --from-prefixes', True),
    ('collision-sampling prefix-population 8 7', False),
    ('collision-sampling stopped-cost 5 6', False),
    ('field-observation shells 1:2,3 --from-prefixes', False),
    ('field-observation clocks 4 0 1 0 1 --matrix --matrix', False),
    ('field-observation clocks 4 0 1,2 0,0 1,-1', True),
    ('field-observation segments 4 0 0 0 1 0', True),
    ('field-observation work 1/2,1/2,0 0,1/3,2/3 1,-1,2 0,1,-1', True),
    ('field-observation invariants 1,1,1,1 0,1,0,0 1,-2,1,0 0,1,-2,1', True),
    ('field-observation native-cycle 4 1,0', True),
    ('field-observation tail-bound 89 2 3 -1/10', True),
    ('collision-sampling grid 4 25 1/2', True),
    ('collision-sampling decomposition 31 2', True),
    ('collision-sampling prefix-word 8 3', True),
    ('collision-sampling shells 121 10', True),
    ('native-refinement detector 4 --json', True),
    ('native-refinement transport 4 --json', True),
    ('native-refinement packet 2 --json', True),
    ('native-refinement mask-capture 20 48 10', True),
    ('native-refinement divisor-work 2 64', True),
    ('weighted-remainder-state alignment-lcm 6 12 12 12', True),
    ('weighted-remainder-state law-characteristic 5 1/3', True),
    ('field-observation segments 4 0 1/2 1 0 1', False),
    ('native-refinement probe-transport 2 --json', True),
    ('native-refinement detector 101', False),
    ('collision-sampling prefix-word 8 7', False),
    ('native-refinement probe-transport 9 --json', False),
]

with tempfile.TemporaryFile(mode='w+') as log:
    with socket.socket() as sock:
        sock.bind(('127.0.0.1', 0))
        port = sock.getsockname()[1]
    daemon = subprocess.Popen([BIN, 'daemon', '--port', str(port), '--threads', '1'],
                              stdout=log, stderr=log)
    try:
        for attempt in range(100):
            if daemon.poll() is not None:
                log.seek(0)
                raise AssertionError(log.read())
            try:
                with socket.create_connection(('127.0.0.1', port), timeout=.5):
                    break
            except OSError:
                time.sleep(.05)
        else:
            raise AssertionError('local daemon did not become ready')
        for command,expected_success in COMMANDS:
            cli = subprocess.run([BIN, *shlex.split(command)], capture_output=True,
                                 text=True, timeout=45)
            with socket.create_connection(('127.0.0.1', port), timeout=45) as conn:
                conn.sendall((json.dumps({'cmd': command}) + '\n').encode())
                response = json.loads(conn.makefile('r').readline())
            assert (cli.returncode == 0) == expected_success, (command, cli)
            assert response['output'] == cli.stdout + cli.stderr, (command, response, cli)
    finally:
        daemon.terminate()
        try:
            daemon.wait(timeout=10)
        except subprocess.TimeoutExpired:
            daemon.kill()
            daemon.wait(timeout=10)
print(json.dumps({'transport_checks': len(COMMANDS), 'passed': True}))
