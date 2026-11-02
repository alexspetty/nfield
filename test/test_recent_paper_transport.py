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
    'collision-sampling inspect 11',
    'collision-sampling poles 11',
    'collision-sampling collar 11 2',
    'collision-sampling prefix 11 4 7',
    'collision-sampling correlation 12 5 0',
    'collision-sampling state 11 7',
    'collision-sampling switching 11 --carriers 2,4,7',
    'collision-sampling convolution 11 7',
    'collision-sampling transform 12 6',
    'collision-sampling inverse 12 6 20',
    'boundary-spectrum inspect 24 --support 0,1,5,8',
    'boundary-spectrum channel 16 3 --weights 0=1:2,3=-1:0',
    'capacity-generation seed 6 12',
    'capacity-generation profile 12 3/2 -5/3,7/4,-1/2',
    'capacity-generation lattice 2/3 12',
    'capacity-generation measurement 5 1 2 4 -3/2',
    'collision-sampling sampled 307',
    'collision-sampling inspect 15',
    'collision-sampling switching 11 --carriers 0',
    'boundary-spectrum inspect 24 --weights 0=nan:0',
    'capacity-generation profile 7 1 2,',
    'capacity-generation lattice 0 4',
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
        for index,command in enumerate(COMMANDS):
            cli = subprocess.run([BIN, *shlex.split(command)], capture_output=True,
                                 text=True, timeout=45)
            with socket.create_connection(('127.0.0.1', port), timeout=45) as conn:
                conn.sendall((json.dumps({'cmd': command}) + '\n').encode())
                response = json.loads(conn.makefile('r').readline())
            assert (cli.returncode == 0) == (index < 17), (command, cli)
            assert response['output'] == cli.stdout + cli.stderr, (command, response, cli)
    finally:
        daemon.terminate()
        try:
            daemon.wait(timeout=10)
        except subprocess.TimeoutExpired:
            daemon.kill()
            daemon.wait(timeout=10)
print(json.dumps({'transport_checks': len(COMMANDS), 'passed': True}))
