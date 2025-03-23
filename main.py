import random
from kernel import BDDCombSim
from math import pi

Sim = BDDCombSim(5, 3)
Sim.init_basis_state(16)
Sim.CNOT(0, 1)
Sim.CNOT(1, 2)
Sim.X(0)
Sim.CNOT(0, 3)
Sim.CNOT(1, 3)
Sim.CNOT(0, 4)
Sim.CNOT(2, 4)
out1 = 1
out2 = 1
Sim.measure([3], [out1])
Sim.measure([4], [out2])
if out1 == 1:
    Sim.X(3)
if out2 == 1:
    Sim.X(4)
if out1 == 1 and out2 == 1:
    Sim.X(0)
if out1 == 1 and out2 == 0:
    Sim.X(1)
if out1 == 0 and out2 == 1:
    Sim.X(2)

Sim.print_state_vec()
print('Finally, r = %d.' % Sim.r)
