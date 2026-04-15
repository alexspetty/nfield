# The Structure That Survives

People ask about the name.

Why *collision invariant*? Why use a phrase that already lives in physics?

Yes. The echo is intentional. But the name was not chosen for ornament. The mathematics pushed me there.

Take a prime $p$ in base $b$. Long division sends each remainder $r$ to a digit by the rule

<div>
$$
\delta(r) = \left\lfloor \frac{br}{p} \right\rfloor.
$$
</div>

That is a schoolroom operation. It takes a remainder and gives back the next digit. Nothing in it announces analytic number theory. Nothing in it suggests conservation laws or Fourier decompositions or $L$-functions.

Now do one more thing. Pick a multiplier $g$ from the units mod $p$. Multiply every remainder by $g$ and sort again by digit bin. Most residues move. Some stay where they were. Those are the collisions.

At first this looks small. A residue either stays in its bin or it does not. Count the ones that stay. That should have been the whole story.

It was not.

Once the collisions were centered, they began to settle into a rigid object. The count was not wandering freely across the primes. It was controlled by a finite table. Complementary classes paired exactly. Later the same object decomposed over Dirichlet characters and reached weighted $L$-values. The local motion looked noisy. The aggregate did not.

That is why I called it the collision invariant. The longer companion note, [The Noble Gas of Primes](https://github.com/alexspetty/nfield/blob/main/publication/drafts/the_noble_gas_of_primes.pdf), is an expository paper about that analogy and why I kept the name.

In physics, a collision invariant is not one particle striking another. It is the part that survives after the collisions have been absorbed into the whole gas. It is the quantity the local chaos does not destroy.

The arithmetic version has the same shape. Residues move. Bins fluctuate. Individual collisions come and go. But something survives the churn and can be named cleanly.

I was not looking for a metaphor. I was looking for that.

This is why the prime case felt clean. At a prime modulus, the nonzero residues form a single multiplicative group. Multiplication permutes that group without the factor-mixing that appears at composite moduli. The geometry is exposed before it is entangled. If the collision laws were going to show themselves anywhere, they were going to show themselves there first.

After that, primes looked different to me. A prime was still a prime in the classical sense. But in a fixed base it was carrying more structure than indivisibility alone had led me to expect. Long division was leaving behind a finite arithmetic shape.

The reflection identity made that hard to ignore. In the finite table, complementary classes satisfy

<div>
$$S(a) + S(m-a) = -1$$
</div>

with no exceptions.

This is not momentum conservation. Nothing physical is being transported from one side to the other. But the experience is similar. What first looks like a system with many degrees of freedom turns out to be locked by a simple reciprocal law. Every peak has a valley. Every arithmetic echo has its mirror.

That was the turn. The object stopped looking like a clever statistic and started looking like a structural one.

From there the program moved the way it had to move. Long division led to collisions. Collisions led to a finite signed table. The table led to reflection. Reflection led to the transform. The transform led to the spectrum. I did not build that chain backward from the Riemann Hypothesis. I followed it forward from a smaller question. If the local arithmetic looks chaotic, what survives?

That is the real reason I kept the name.

The phrase *collision invariant* answers a question people ask me, but it also names the research impulse behind the program. I keep returning to the point where a small finite mechanism stops looking accidental and starts looking structural. I am interested in the part that remains when everything else has been allowed to move.

So when I use the phrase, I do mean to invoke physics, but with limits.

I do not mean that primes are particles.
I do not mean that the reflection identity is literally momentum conservation.
I do not mean that number theory can be reduced to fluid mechanics.

I mean that the same pattern appears in both places. Local collisions, global law. Microscopic noise, macroscopic structure. Apparent disorder, one thing left standing.

That pattern is not the whole content of the collision program. But it is one of the deepest reasons the program exists.

Paper: [The Noble Gas of Primes](https://github.com/alexspetty/nfield/blob/main/publication/drafts/the_noble_gas_of_primes.pdf)

*Alexander S. Petty*
April 2026
.:.
