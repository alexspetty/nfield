# Partial Character Sums and the Collision Transform

**Preprint, submitted to arXiv**

The first three papers worked at a fixed modulus: $b^2$. The characters were modulo $b^2$. The decomposition theorem factored the Fourier coefficients at that modulus. Everything was clean because $b^2$ has a special structure.

This paper asks: what happens at the modulus $n$ itself?

When $n$ is a prime, the characters modulo $n$ are the natural ones. When $n = pq$ is a semiprime, the characters factor through the Chinese Remainder Theorem as $\chi = \chi_p \times \chi_q$. The collision transform at modulus $n$ sees the factorization. The question is whether it can read it.

## The bin character sum identity

The answer starts with a three-line proof. For any integer $n > b$ and any Dirichlet character $\chi$ modulo $n$:

<div>
$$\hat{C}_n(\chi) = \frac{1}{\phi(n)} \sum_{d=0}^{b-1} |A_d(\chi)|^2$$
</div>

where $A_d(\chi) = \sum_{r \in B_d} \chi(r)$ is the partial character sum over the $d$-th bin of the digit function.

The collision transform equals the sum of squared partial character sums over the bins. The proof is a substitution: set $s = gr$ in the double sum, and the collision condition becomes a bin-membership condition. The terms regroup by bin and the identity falls out.

This holds at every modulus. Prime, composite, prime power. No restriction on $\chi$. No primitivity assumption. The identity is Parseval applied to the digit function's bin decomposition.

## Why this matters

The partial character sums $A_d(\chi)$ are the central objects of analytic number theory. Polya and Vinogradov bounded them in the 1910s. Burgess sharpened the bounds in the 1960s. Every advance in understanding partial character sums over intervals produces consequences for prime distribution, cryptography, and computational number theory.

The bin character sum identity says: the collision transform IS these sums. The collision invariant, defined by counting digit-bin coincidences, decomposes into the same objects that Polya, Vinogradov, and Burgess spent a century studying. The digit function connects the collision program to the classical theory through an exact identity.

## Ghost collisions

At composites, something unexpected happens. Nearly all collisions are ghosts.

A ghost collision at $n = pq$ is a collision at the composite (two remainders sharing a digit bin under multiplication) that does not exist at either prime individually. The composite's wider bins absorb shifts that the primes' narrower bins reject.

| $n$ | factorization | ghost % |
|-----|--------------|---------|
| $77$ | $7 \times 11$ | $100.0$ |
| $91$ | $7 \times 13$ | $100.0$ |
| $143$ | $11 \times 13$ | $100.0$ |
| $221$ | $13 \times 17$ | $99.4$ |
| $667$ | $23 \times 29$ | $98.7$ |

At $n = 77$: every single collision is a ghost. Neither prime contributes any inherited collisions. The composite's collision structure is entirely its own creation, arising from the interleaving of the two primes' digit geometries through the floor function.

## The interleaving

For $n = pq$, each bin character sum $A_d(\chi_p \times \chi_q)$ is a bilinear form: $\chi_p^T M_d \chi_q$, where $M_d$ is the binary matrix recording which CRT pairs $(i, j)$ fall in bin $d$. If the collision transform factored as a tensor product of the transforms at $p$ and $q$, the bin matrices would be rank 1. They are not.

At $n = 91 = 7 \times 13$ in base 10: the bin matrices have rank 5 or 6 (out of a maximum of 6). The singular values are structured but the matrices are far from rank 1. The composite collision spectrum carries information about the interaction between the two primes' digit geometries that cannot be recovered from either prime's spectrum alone.

The factoring information is in the $A_d$. The bin character sum identity says the collision transform is the sum of their squared magnitudes. The phases are lost in the squaring. Whether the phases, recoverable through cross-bin correlations, can constrain the factorization is an open question.

## The wall

Every approach to extracting factors from the collision invariant hits the same limit: the factoring signal is a $1/p$ perturbation in a quantity of order 1. The Euler factor at a prime $p$ has magnitude $|1 - \chi(p)/p|^{-1} \approx 1 \pm 1/p$. Detecting that perturbation in a product of infinitely many terms requires precision proportional to $p$, which costs $O(p)$ operations. The wall is fundamental, not an artifact of the approach.

But the bin character sum identity changes the terrain. The factoring problem is now stated as: evaluate partial character sums over intervals of length $n/b$, where the character factors through CRT. This is squarely in the domain of analytic number theory. The collision invariant has translated a factoring problem into a character sum estimation problem. That translation is new.

The digit function projects a two-dimensional structure (the CRT grid of a semiprime) onto a one-dimensional assignment (the digit). The bins are the projection. The partial character sums are the components. The collision transform is their combined energy. The factoring information is distributed across all $n$ residues, and no local observation concentrates it. But the language in which the problem is now stated is the language where number theorists have built their most powerful tools.

Code: [github.com/alexspetty/nfield](https://github.com/alexspetty/nfield)

*Alexander S. Petty*
April 2026
.:.

