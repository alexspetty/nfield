# Draft: alexpetty.com about text

**The Collision Program** is a body of number-theory research Alex discovered and has developed across several papers and preprints, documented on this site.

The digit function $\lfloor br/p \rfloor$ assigns a digit to each remainder during long division. It is trivially defined and universally familiar. It is also a bridge between the additive structure of the integers (bins, intervals, floor functions) and their multiplicative structure (characters, L-functions, prime distribution).

The program studies the collision invariant: a count of how many remainders share a digit bin with their image under multiplication. This count decomposes into Dirichlet characters through an exact identity, the decomposition theorem, which factors each Fourier coefficient into a generalized Bernoulli number (encoding an L-function special value) and a diagonal character sum (encoding the bin geometry). The collision weights are proportional to $|L(1,\chi)|^2$.

Several results in this program connect to the zeros of L-functions. These connections are conditional: the collision framework provides equivalences and reductions, not proofs of GRH (yet).

The proved results include the gate width theorem (exactly $b-1$ deranging multipliers at every prime, via an explicit rational family), the collision table and its antisymmetry, the diagonal--Bernoulli identity at special bases, a Parseval moment identity giving an exact formula for a weighted second moment of $|L(1,\chi)|^2$, and conditional convergence estimates for the collision fluctuation sum.

All results are supported by [nfield](https://github.com/alexspetty/nfield), an open-source analysis engine written in C.

## Publications

- [The Collision Invariant](https://arxiv.org/abs/2604.00045) (2026). Gate width theorem, finite determination, reflection identity, half-group theorem.
- [The Collision Transform](https://arxiv.org/abs/2604.00047) (2026). Antisymmetry, centered convergence at s=1, conditional penetration, neutrality.
- [The Collision Spectrum](https://arxiv.org/abs/2604.00054) (2026). Decomposition theorem, L-encoding, Parseval moment identity, correlation decay.
- [A Diagonal--Bernoulli Identity for Collision Weights](https://github.com/alexspetty/nfield/blob/main/publication/a_diagonal_bernoulli_identity.pdf) (2026, preprint). The collision table with antisymmetry, the diagonal--Bernoulli identity at bases 6, 10, and 12, fourth-moment relation, Q(√5) structure of base-10 weights.
- [Convergence of Collision Fluctuation Sums](https://github.com/alexspetty/nfield/blob/main/publication/convergence_of_collision_fluctuation_sums.pdf) (2026, preprint). Conditional convergence in Re(s) > 1/2 under GRH, avoidance deficit, Q(√5) reduction.

## About the Author
![Alexander S. Petty](https://alexpetty.com/content/images/2026/03/asp1.jpg)
Alex is the founder and CEO of [Boston Agile Labs](https://bostonagilelabs.com), a management consulting firm helping large organizations align strategy with execution in the AI era. The firm works with Fortune 500 enterprises and federal agencies on organizational redesign for AI, executive coaching, operating-model design, and intent-governed delivery. Alex was an early [signatory of the Agile Manifesto](https://agilemanifesto.org/display/000000057.html) and has spent two decades closing the gap between what organizations intend and what they actually deliver, inside institutions like T. Rowe Price, FM Global, Freddie Mac, BCG, Capital One, John Hancock, and others. He is the author of *The Living Organization* and *The AI Transformation Playbook*. He has several patents pending on computational methods for AI identity and recursive structure.

He lives in Virginia.
