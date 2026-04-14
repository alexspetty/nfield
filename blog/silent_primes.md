# Silent Primes and the Variance of the Collision Count

Sit down at a desk with a sharpened pencil, a sheet of paper, and a prime number. Pick a small one. Thirteen will do.

Divide one by thirteen the long way, the way you learned in school. Write the digits as they come. After a few steps you find that the digits start repeating: zero, seven, six, nine, two, three, zero, seven, six, nine, two, three, and on it goes, forever. Six digits in the repeating block, then back to the beginning. This block, $076923$, is what mathematicians call the *repetend* of the fraction $1/13$. It is the part of the decimal that loops, and it is the soul of the prime as far as base ten is concerned.

Now do something a child might do. Cut the repetend out, paste it onto a thin strip of paper end to end so you have a long ribbon with the same six digits repeating across it. Make a second copy. Lay one ribbon on top of the other so the digits line up perfectly. Then slide the top ribbon to the right by one position and look at the two ribbons together.

What you see is two rows of digits stacked, position by position. Compare them down the line. Where the digit on top equals the digit on bottom, you have a *match*. Count the matches.

For the prime $13$, the count is zero. Not one match. The two ribbons, written out from the same six digits in different rotations, share no common digit at any position. They are perfectly mismatched. Even random sliding would be expected to produce one or two accidental matches. This produces none. The mismatch is total.

Try the prime $17$. Its repetend is sixteen digits long ($0588235294117647$). Cut a strip, make a copy, slide one position over, and count. The answer is positive. A few of the sixteen positions happen to share their digit with the slid copy.

Try $19$. Eighteen-digit repetend. Slide one. Count. Zero again. None of the eighteen positions match.

Try $23$. Twenty-two digits. Slide one. Count. Zero.

Try $29$. Twenty-eight digits. Slide one. Count. Positive.

Try $37$. Zero. Try $41$. Zero. Try $43$. Positive. Try $47$. Positive. Try $53$. Positive. Try $73$. Zero.

If you keep going, walking up through the primes one at a time, sliding the ribbon by one position and counting the matches, you find that *most* primes give a small positive number, in the neighborhood of one or two or three. But a handful of primes give exactly zero. The ribbon and its shifted copy refuse to overlap at any position whatsoever, not even by accident. I started calling these primes *silent*. Silent because the signal, the count of matches between the loop and its shift, is not partially gone or mostly gone. It is fully gone. There is nothing to hear.

The natural question is which primes are silent, and whether there is a way to know in advance without checking each prime one by one.

## A list and a formula

Walk through every prime up to a thousand and write down the silent ones. The list comes out short:

$$\{11,\ 13,\ 19,\ 23,\ 37,\ 41,\ 73\}.$$

Seven primes. After $73$, no more silent ones at this slide. Walk all the way up to a million primes, ten million, a billion. The list does not grow. There are exactly seven primes greater than ten that are silent under a one-position slide in base ten. Forever.

That, on its own, is the first surprise. There are *finitely* many silent primes, and you can list them with seven entries. Past the seventh, the universe of primes goes on without producing another one.

The second surprise is that you do not need to walk through every prime to find the list. There is a recipe that produces it. And the recipe is not a lucky guess. It falls out of the previous paper, [bin derangements](https://alexpetty.com/bin-derangements-and-the-gate-width-theorem/), with one line of algebra.

Let me back up and explain how I found it, because the path from the previous paper to the recipe is the part that makes the rest of the paper feel inevitable instead of magical.

The previous paper proved a clean structural fact about deranging multipliers. At any prime $p$ in base ten, there are exactly nine multipliers that move every residue out of its original digit bin (the count is nine because the base is ten; in general it is $b - 1$). And those nine multipliers are not random. They are nine specific *rational numbers*, the same nine for every prime, just reduced modulo the prime in question. Here are the nine rationals in base ten:

$$-\tfrac{1}{9},\quad -\tfrac{1}{4},\quad -\tfrac{3}{7},\quad -\tfrac{2}{3},\quad -1,\quad -\tfrac{3}{2},\quad -\tfrac{7}{3},\quad -4,\quad -9.$$

At each prime $p$, you reduce these nine rationals modulo $p$ (which means inverting the denominators inside the integers mod $p$, since fractions do not literally make sense as integers but their reductions do). The result is nine specific residues at each prime, and those residues are exactly the deranging multipliers there. The list of nine rationals is the *same* list at every prime. The reductions are different.

Now think about what it means for $p$ to be silent at slide one. Silence at slide one means the multiplier $g = 10$ falls in the deranging set. The deranging set is the reduction of the nine rationals modulo $p$. So silence means $10$ has to equal one of the nine rationals reduced mod $p$. At least one of them. Pick one and write the condition down. Take the rational $-u/(10 - u)$, where $u$ is one of $1, 2, \ldots, 9$. The silence condition is

$$10 \equiv -\frac{u}{10 - u} \pmod{p}.$$

This is the moment the recipe falls out, and it falls out from the most natural move you can make with this equation. Multiply both sides by $(10 - u)$ to clear the fraction. The left side becomes $10(10 - u) = 100 - 10u$. The right side becomes $-u$. Subtract the right side from the left:

$$100 - 10u - (-u) = 100 - 9u.$$

The condition is that this number, $100 - 9u$, is divisible by $p$. That is the entire derivation. Clear one fraction, simplify, read off the integer.

So $p$ is silent at slide one in base ten if and only if $p$ divides one of the integers $100 - 9u$ for $u = 1, 2, \ldots, 9$. The recipe is the result of clearing exactly one fraction in a condition that came from the previous paper. Nine rationals from the gate width theorem. Nine cleared denominators. Nine integers to factor.

Here is the recipe one more time, in plain language. Compute $100 - 9$. Then $100 - 18$. Then $100 - 27$, and so on, subtracting another $9$ each time, until you have walked through nine subtractions. You get nine numbers:

$$91,\quad 82,\quad 73,\quad 64,\quad 55,\quad 46,\quad 37,\quad 28,\quad 19.$$

That is the list. Now factor each of the nine numbers and read off the prime factor that is greater than ten. (Sometimes the number is itself a prime greater than ten, in which case the factor and the number are the same. Sometimes the number factors only into primes that are too small to count, in which case it contributes nothing.)

```
value    factored      silent prime
-----    ----------    ------------
  91     7 × 13              13
  82     2 × 41              41
  73     prime               73
  64     2^6                 none
  55     5 × 11              11
  46     2 × 23              23
  37     prime               37
  28     2^2 × 7             none
  19     prime               19
```

Read down the rightmost column. Throw out the two "none" rows, since they did not contribute anything new. Collect the seven primes that remain: $13$, $41$, $73$, $11$, $23$, $37$, $19$. Sort them in increasing order: $11$, $13$, $19$, $23$, $37$, $41$, $73$. These are exactly the seven silent primes I listed at the top of this section. Every single one, recovered by hand, from a recipe that took less than five minutes to apply.

What this means is striking. Silent primes are not a hidden subset of the primes that you have to discover one at a time by computation. They are the prime divisors of nine specific small integers. Past the last factor, no further silent primes exist. The mystery of "which primes are silent" has the kind of answer most number theory questions never have. A finite list. An exact recipe. No exceptions.

The recipe generalizes. At a slide of two positions (instead of one), the integers to factor are $1000 - 99$, $1000 - 198$, $1000 - 297$, and so on. At a slide of three positions, $10000 - 999$, $10000 - 1998$, and so on. At every slide, a finite list. At every slide, an exact recipe. The silent primes at any slide in any base are the prime divisors of a small arithmetic progression that depends only on the base and the slide.

For the moment, set the silent primes aside. They look like a finished story. A finite list, an exact recipe, no further entries. The kind of result you can hold in your hand and put down. That is exactly how I treated them when I first found the formula.

That view is wrong, and the rest of this paper is going to correct it. The seven silent primes in base ten are not seven curiosities. They are the *extreme case* of something much larger that runs across every prime, and the second half of this paper is what measures the larger thing. The silent primes are where the larger thing happens to hit its furthest boundary. They are not a side observation. They are the tail of a distribution.

What that distribution is, and why the silent primes are at its tail, takes a little setup. Let me show it to you.

## The wobble

Most primes are not silent. They give a positive count when you slide the ribbon by one position and tally the matches. The count varies from prime to prime. At one prime it might be six, at the next four, at the next nine. The variation is what the second half of the paper is about.

Look at the data. Take a long list of primes, walk up through them, write down the count for each one alongside something else: the *bin size*, which is roughly the prime divided by ten. (For technical reasons the bin size is the number of digits in the repetend divided by ten, but for primes where the repetend is as long as it can be, the two amount to the same thing.) The bin size is the *expected* count, in the sense that if collision matches were spread evenly across the slide positions, the count would equal the bin size. So the count and the bin size should be near each other, and the question is how near.

Here are a few primes in base ten with their bin sizes and their actual counts:

```
prime p     bin size Q     count C(10)
-------     ----------     -----------
   97            9             6
  193           19            14
  499           49            40
  997           99            84
 1999          199           173
 4999          499           440
 9973          997           885
```

The counts are *near* the bin sizes but never equal. At $p = 97$, the bin size is $9$ and the count is $6$, below by $3$. At $p = 1999$, the bin size is $199$ and the count is $173$, below by $26$. At $p = 9973$, the bin size is $997$ and the count is $885$, below by $112$.

The counts are wobbling around their expected values. At small primes the wobble is small in absolute terms but still a substantial fraction of the bin size. At large primes the wobble grows in absolute terms, but as a fraction of the bin size it shrinks. The deviations are not random in any visible way; they have structure, and the question is what that structure looks like.

The most natural way to ask the question is to take the deviation, square it, and average over many primes. That gives the *variance* of the count. The square root of the variance gives the *standard deviation*, which is the typical size of the wobble.

Compute the standard deviation across all primes up to ten thousand and divide by the square root of the bin size $Q$. Here is what comes out:

```
prime p     bin size Q     standard deviation / √Q
-------     ----------     -----------------------
    97            9               0.817
   193           19               0.857
   499           49               0.909
   997           99               0.923
  1999          199               0.933
  4999          499               0.940
  9973          997               0.942
```

The numbers in the right column are climbing toward something. They start in the low $0.8$s and walk up steadily, slowing down as they climb. By the time you have ten thousand primes in the calculation, the ratio is about $0.94$, and the slowing-down strongly suggests it converges to some constant in the neighborhood of $0.94$ or $0.95$.

What this means is that the wobble of the count, measured properly, is *exactly the square root of the bin size*, with some constant in front that depends only on the base. Not the bin size itself. Not a constant. The square root.

And now you can see what the silent primes were. The collision count usually wobbles around its mean by something on the order of $\sqrt{Q}$. The seven primes from the first half were the special cases where the wobble happened to hit *exactly* the bottom of its possible range. The count fell all the way to zero, the largest possible negative excursion the wobble can take. Silent primes are not seven oddities. They are the extreme case of the wobble, the primes where the deterministic comparisons inside the count happened to all line up the same way at once and reach the boundary. They are the tail of the distribution that the wobble describes.

This is the connection I promised at the end of the first half. The seven primes that gave zero are not a side curiosity. They are the seven places where the wobble in base ten ran out of room.

If you have not seen the square root before in this kind of context, the next section will not feel like much. Stay with me, because the square root is everything.

## Like the Riemann Hypothesis

A few minutes of detour is needed here, because the wonder of the square root requires a piece of context from a different part of mathematics.

There is a function in number theory called the *prime counting function*. It is exactly what it sounds like. For any number $x$ you choose, the prime counting function tells you how many primes are less than or equal to $x$. Mathematicians write it as $\pi(x)$. So $\pi(10) = 4$ (the primes up to $10$ are $2, 3, 5, 7$), $\pi(100) = 25$, $\pi(1000) = 168$, $\pi(10000) = 1229$, and on it goes.

The famous *prime number theorem*, proved at the end of the nineteenth century by Hadamard and de la Vallée Poussin (independently of each other, in the same year, by similar methods), says that $\pi(x)$ is approximately equal to $x$ divided by the natural logarithm of $x$. As $x$ grows, the approximation gets better. There is a slightly more accurate approximation involving an integral called the *logarithmic integral* $\mathrm{li}(x)$, but the basic story is the same. The prime counting function has a smooth approximation, and the approximation gets better as the prime grows.

The approximation is not exact. There is an error. The difference between $\pi(x)$ and $\mathrm{li}(x)$ is not zero. The size of this error is one of the central questions of analytic number theory, and it has been the central question for a hundred and sixty years.

The Riemann Hypothesis is the conjecture that the error is bounded by a particular shape. Specifically, the conjecture predicts that the difference between the actual count and the smooth approximation is at most about the square root of $x$, times a logarithmic factor. The Riemann Hypothesis says the error is on the order of $\sqrt{x}$, give or take some logarithms.

Why is the square root the threshold? Because anything smaller than $\sqrt{x}$ would force the primes to be more regular than they have any right to be, and anything larger than $\sqrt{x}$ would force them to be more chaotic than the analytic machinery can tolerate. The square root is the boundary between *as much structure as you could hope for* and *more chaos than the proof permits*. It is the conjectured exact size of the deviation from the smooth answer.

The Riemann Hypothesis has been unproved for a hundred and sixty years. It is the most famous unsolved problem in mathematics. Many mathematicians have spent their careers chasing it. There is a million-dollar prize for the first person to settle it. Generations of analytic number theory have grown up around its edges. The square root is the heart of the conjecture. Whoever proves the Riemann Hypothesis proves that the primes deviate from their smooth approximation by exactly that much, no more, no less.

Now come back to the collision count. The wobble of the collision count, measured by the standard deviation, is *also* approximately the square root of the bin size. Not the bin size. Not a constant. The square root. The same shape, the same threshold, the same fingerprint that the Riemann Hypothesis predicts for the prime counting function.

I want to be careful here. The collision count is not the prime counting function. The bin size is not $x$. The two phenomena live in different parts of the mathematical landscape, and there is no direct way to derive one from the other. But the *shape* of the deviation is the same, and the shape is what matters in this kind of question.

What this suggests, but does not prove, is that the same kind of analytic structure that controls the prime counting function also controls the collision count. The Riemann Hypothesis is about the zeros of a particular function called the Riemann zeta function, and those zeros appear to govern the deviations of $\pi(x)$ from $\mathrm{li}(x)$. The hope behind this paper is that some similar analytic structure, some similar list of zeros in some related function, governs the deviations of the collision count from its bin size. If the hope is real, the digit function and the Riemann zeta function are looking at the same skeleton from two different angles.

Right now the hope is just a hope. The square-root scaling of the collision count is a numerical conjecture, supported by computation but not proved. The connection to a hidden $L$-function is suggested by the matching square-root shape but not established. This paper points at the hope. The next paper picks it up.

## A note from 2026

*April 2026*

Looking at this paper now, the central observation has held up and the central conjecture has gotten sharper. The square-root variance scaling for the collision count was verified well past the original computation, and the constant in front of the square root now has a closed-form expression in terms of the elementary geometry of the digit function. The variance conjecture is no longer just a numerical observation. It has a structural reason, and the reason is that the deterministic comparisons inside the collision count behave like a sum of weakly correlated coin flips whose decorrelation is controlled by the equidistribution of certain residues modulo the prime.

The connection between the silent primes and the wobble of the rest of the primes (which I drew explicitly above when I wrote this version of the paper) was a connection I did *not* see at all when I wrote the original research note. At the time, the two halves of the paper felt like two separate observations that happened to live in the same write-up. It took a while to realize that the silent primes are the tail of the same distribution the wobble measures, and that asking about silence is asking about the tails. The version above, which presents the two halves as one continuous story, is the way I would write the paper today. The original research note keeps them separated.

The hope at the end of the paper, that the collision count and the prime counting function are governed by the same kind of analytic structure, turned out to be partially right and partially wrong. The right part: the collision count *does* connect to L-function values, through a mechanism I worked out in [the character structure of the collision fluctuation](https://alexpetty.com/the-character-structure-of-the-collision-fluctuation/) and made precise in [the collision spectrum](https://alexpetty.com/the-collision-spectrum/). The wrong part: the connection is not to the same L-function zeros that govern the prime counting function. It is to L-function *special values* at $s = 1$, which come from the elementary side via Bernoulli numbers. The mechanism is real. It is just not exactly the mechanism I was guessing at the time.

The square-root scaling itself has not been upgraded to a theorem. It remains a conjecture. In some sense it is the analog of the Riemann Hypothesis for the collision count. A precise quantitative statement about a fluctuation, supported by all the data, plausible from the structural arguments, and not yet proved.

.:.

---

## Try it yourself

```
$ ./nfield silent_primes 10 --lag 1
  base 10, lag 1
  recipe: 100 - 9u for u = 1..9
  values: 91, 82, 73, 64, 55, 46, 37, 28, 19
  prime factors > 10: {11, 13, 19, 23, 37, 41, 73}
  total silent primes at lag 1 in base 10: 7

$ ./nfield silent_primes 10 --lag 2
  base 10, lag 2
  recipe: 1000 - 99u
  values: 901, 802, 703, ..., 109
  silent primes (first few): 13, 17, 19, 29, 37, 53, 101, ...

$ ./nfield variance 10 --primes 10000
  base 10, all primes p ≤ 10000
  σ(C) / √Q ≈ 0.942
  approaching a constant, slow climb
```

Three commands. The first two compute the silent primes at slides one and two from the recipe. The third computes the wobble across ten thousand primes and reports the ratio. The first two are exact and finite. The third is asymptotic and conjectural.

Code: [github.com/alexspetty/nfield](https://github.com/alexspetty/nfield)
Paper: [Silent Primes and the Variance of the Collision Count](https://github.com/alexspetty/nfield/blob/main/research/silent_primes.pdf)

---

*Alexander S. Petty*
January 2023 (updated April 2026)
.:.
