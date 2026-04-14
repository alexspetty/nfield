# Phase-Filtered Ramanujan Sums and the Spectral Gate

Take a small prime, ask [nfield](https://github.com/alexspetty/nfield) for the loop of $1/p$ in base $10$, and watch what comes back.

```
$ ./nfield field 7
  1/7 => 0.|142857| (closed)

$ ./nfield field 11
  1/11 => 0.|09| (closed)

$ ./nfield field 13
  1/13 => 0.|076923| (closed)

$ ./nfield field 17
  1/17 => 0.|0588235294117647| (closed)
```

My computer-friendly notation for a repeating sequence is to wrap it in pipes, since the overbar that mathematicians use for repeating decimals does not survive a copy-paste from a terminal. So $0.|142857|$ is the same thing as $0.\overline{142857}$, just typed in a way the shell can read. Look at the four loops side by side. Six digits at $p = 7$. Two digits at $p = 11$. Six digits at $p = 13$, six again but a completely different six in a different order. Sixteen digits at $p = 17$, almost the full $p - 1 = 16$ residues showing through.

Different primes, different loops. Nothing surprising about that. Every prime has its own decimal expansion and they are all a little different from one another. What is surprising is what happens when you start asking simple questions about those loops, and find that the answers cluster the primes into a small finite number of families, sorted by their last digit.

The prime $11$ ends in $1$. The prime $13$ ends in $3$. The prime $17$ ends in $7$. The loop of $1/11$ responds to shifting in one way. The loop of $1/13$ responds in a different way. The loop of $1/17$ responds in a third way. And here is the puzzle. Any other prime ending in $1$, like $31$ or $41$ or $71$, responds *the same way* as $11$. Any other prime ending in $3$, like $23$ or $43$ or $53$, responds the same way as $13$. The last digit of a prime, which seems like the most superficial thing about it, is doing the work of a fingerprint.

This paper is where I figured out why.

The story starts with a count. For each prime, you can ask how often the loop of $1/p$ matches a shifted copy of itself. Lay the loop down on a table, slide it by one position, and count the agreements between the shifted loop and the original. Then slide by two positions, three, four, all the way around. The result is a sequence of small integers, one per shift, called the autocorrelation of the loop. The autocorrelation is a kind of structural signature of the prime, and small primes have surprisingly tight signatures. For $1/7$ every nontrivial shift gives zero matches. For $1/29$ most shifts give zero but a handful give one or two or four. For $1/41$ almost every shift carries a small nonzero value. The signature is concrete data, finite arithmetic, no analysis required to compute it.

In [the autocorrelation formula](https://alexpetty.com/the-autocorrelation-formula/) I worked out a closed formula for these counts. The formula closed the chain from long division to a finite walk through a small table, with no need to compute any digits along the way. Closing the chain was satisfying. But it left me staring at a list of autocorrelation values for every prime, and that list itself was a puzzle. The values were not random. They vanished at certain shifts and not at others, in patterns that seemed deliberate. The pattern of zeros was telling me something about the prime, and I wanted to know what it was saying.

This paper is the answer. The pattern is set by the last digit, and the mechanism is something I had not expected to meet in a chapter about fractions.

## Three primes on the table

The right place to start is in front of the printouts. Here is what nfield prints for the first three primes I asked.

```
$ ./nfield autocorrelation 7
  R(0) = 6
  R(1) = R(2) = R(3) = R(4) = R(5) = 0

$ ./nfield autocorrelation 29
  R(0) = 28
  R(1) .. R(28) =
    0, 1, 2, 0, 0, 1, 4, 0, 1, 2, 0, 0, 0, 0,
    0, 0, 0, 0, 2, 1, 0, 4, 1, 0, 0, 2, 1, 0

$ ./nfield autocorrelation 41
  R(0) = 40
  rich nonzero structure across all 40 nontrivial shifts
```

A few things jump out. At $p = 7$ every nontrivial shift produces a zero. At $p = 29$ most shifts produce zero, but a handful produce $1$, $2$, or $4$. At $p = 41$ the pattern is denser still, with structure at almost every shift.

Common to all three, if you count carefully, the number of vanishing shifts at every prime in base $10$ is exactly nine. Nine zeros at $p = 7$ would have to wrap around (since the loop is shorter than nine), so all five nontrivial shifts get swallowed. Nine at $p = 29$ leaves nineteen non-vanishing shifts. Nine at $p = 41$ leaves thirty-one. The number nine never changes. It is one less than the base, and it does not depend on which prime you pick.

The number is universal. The locations of those nine vanishing shifts are not. That is the puzzle I want to solve.

## A word for the vanishing shifts

Before I could ask why the zeros land where they do, I needed to know what makes a zero a zero. So I went back and looked at exactly what was happening at the vanishing shifts.

The picture is clean. At those shifts, every digit position in the loop of $1/p$ moves to a brand-new digit. None of the digits stays put. Mathematicians call a permutation that moves every element a *derangement*, and the shifts that fully derange the loop are the ones I am after. I will call them the **deranging shifts**.

There are always exactly $b - 1$ of them at any prime in base $b$. That fact is structural. It does not depend on which prime you picked. It depends only on the base.

In base $10$ that means nine deranging shifts at every prime, no matter how big the prime gets. In base $3$ it would be two. In base $2$ it would be one. The width of the gate is set by the base alone.

## The other half

The nine zeros at every base-$10$ prime have a name now and a clean structural reason. The deranging shifts. That is the easy half of the puzzle, accounted for. The hard half is the rest of the autocorrelation, the small nonzero values that fill in everywhere else. At $p = 29$ those leftover values were $1$, $2$, and $4$. At $p = 41$ they crowded almost every shift. They are not random and they are not arbitrary, which means they are built out of *something*. I wanted to know what.

The answer comes from a corner of mathematics that I have always found romantic. In the early years of the twentieth century, a self-taught clerk in Madras filled notebook after notebook with thousands of identities he had derived by methods he could not always explain, attributing them to the goddess Namagiri whispering in dreams. His name was Srinivasa Ramanujan. He posted a few of the identities in a letter to G. H. Hardy at Cambridge in $1913$, and Hardy, after deciding the letter was either from a crank or from a genius and reluctantly concluding it had to be the latter, arranged to bring him to England. Ramanujan died of tuberculosis at thirty-two, having published a handful of papers that mathematicians are still mining today. One of them, from $1918$, introduced a family of finite trigonometric sums that now bear his name.

A *Ramanujan sum* is built out of evenly spaced waves on a circle of integers, with one twist. Only the integers coprime to the modulus contribute, the rest are dropped. The construction looks elementary, almost trivial. It is not. Ramanujan showed that a wide class of arithmetic functions, the things that count divisors and prime factors and the like, can be expanded in his sums the way a periodic signal can be expanded in sines and cosines. Even more striking, when you sum his harmonics across all moduli, the Riemann zeta function falls out the other side. The sums look like little exponential exercises and they are wired straight into the deepest object in analytic number theory.

So when these sums showed up uninvited in my autocorrelation, sitting underneath the formula that had just come out of long division, I paid attention. I had not gone looking for them. They had arrived on their own, and that was the part that made me think the chain I was on was real.

The collision autocorrelation $R(\ell)$ is built out of Ramanujan sums too. But not the plain ones. The version that shows up here is a *filtered* version. Each Ramanujan harmonic carries a phase, and only harmonics whose phases line up in a particular way pass through. The rest are blocked. I will call the object that decides which harmonics pass and which are blocked the **spectral gate**. The autocorrelation is what comes out the other side.

## The gate is binary

The first thing I did once I had a name for the gate was measure it. I ran the gate at every shift, at every prime up to ten thousand, in five different bases, and watched what came out. What I expected was a smooth response curve, the kind every garden-variety filter produces, where some frequencies pass strongly, some weakly, and some not at all.

That is not what I got. At every prime, in every base, the response at any non-self shift was *exactly zero* or *bounded firmly away from zero*. There was no middle ground. No shift produced a faint trickle of signal. Either the harmonic passed in full force or it was completely killed.

That is a sharper claim than I expected. A garden-variety filter degrades smoothly across frequencies. This one does not. A shift either lives or it dies, with no gray zone in between. The gate is more like a series of doors than a window with a curtain.

## Where the gate's shape comes from

A series of doors is a useful image, but doors do not open themselves. Something has to decide which doors are open at any given prime, and I went into this expecting the answer to involve some hard-won structural invariant, the kind of thing you chase through three theorems before you can give it a name. The actual answer was the most elementary fact about a prime that you can write down.

The last digit.

The residue $r = p \bmod b$, the digit a prime ends in when you write it out in base $b$, decides which doors are open and which are closed. In base $10$ a prime past $2$ and $5$ has to end in one of four digits, $1, 3, 7$, or $9$. Every prime in the universe larger than five falls into one of four families, and the family is the last digit. The gate at $11$ is the gate at $31$ is the gate at $41$ is the gate at every other prime ending in $1$, all the way out to infinity. They share a fingerprint that has been sitting on their last digit the whole time, and nobody had noticed it was there.

The mechanism that connects "last digit" to "open doors" is short to state. The residue $r$ controls the tail of the continued fraction expansion of $p/b$. (A continued fraction is an old object from a chapter most schoolteachers no longer teach, the chapter where you unfold a fraction into a chain of integer divisions until something terminates.) That tail picks out which Ramanujan harmonics survive the filter. Different residues mean different tails, different tails mean different filters, different filters mean different gates.

The pipeline runs from the most elementary thing you can know about a prime to the most structural. Last digit, continued fraction tail, surviving harmonics, open doors. Four hops, no analysis, no machinery beyond what Euclid had. The spectral signature of the prime is sitting on its rightmost decimal place, and once you know how to look you can read it off in a glance.

## The four tails of base ten

"The continued fraction tail decides which doors are open" is an answer. It is also the kind of answer that needs a worked example next to it before you can believe it. So let me show you the arithmetic, in full, for one prime. I want you to be able to do this yourself by the end of this section, on any prime you can think of, with nothing in your hand but a pencil.

Pick a prime ending in $3$. I will pick $p = 53$. The continued fraction of $53/10$ is computed by repeated division with remainder, the same trick from the chapter Euclid wrote and your sixth-grade teacher tried to make you care about.

Put $53$ on top, $10$ on the bottom. Divide $53$ by $10$. The quotient is $5$, with a remainder of $3$.

```
53 = 5 · 10 + 3
```

Write down the $5$, set it aside, and now flip the leftover. Divide $10$ by $3$. Quotient $3$, remainder $1$.

```
10 = 3 · 3 + 1
```

Write down the $3$. Flip again. Divide $3$ by $1$. Quotient $3$, remainder $0$.

```
3 = 3 · 1 + 0
```

The remainder hit zero, so the algorithm halts. The quotients you wrote down, in order, were $5$, then $3$, then $3$. Those quotients are the continued fraction of $53/10$. Mathematicians write the result as $[5; 3, 3]$. The number before the semicolon is the integer part of $53/10$. The numbers after the semicolon are the *tail*, the part that does the structural work. For $p = 53$ the tail is $[3, 3]$.

Now do the exact same procedure for another prime ending in $3$. Take $p = 23$.

```
23 = 2 · 10 + 3
10 = 3 · 3 + 1
 3 = 3 ·  1 + 0
```

Quotients in order: $2$, $3$, $3$. Continued fraction $[2; 3, 3]$. Tail $[3, 3]$.

Take $p = 43$.

```
43 = 4 · 10 + 3
10 = 3 · 3 + 1
 3 = 3 · 1 + 0
```

Continued fraction $[4; 3, 3]$. Tail $[3, 3]$.

Take $p = 13$.

```
13 = 1 · 10 + 3
10 = 3 · 3 + 1
 3 = 3 · 1 + 0
```

Continued fraction $[1; 3, 3]$. Tail $[3, 3]$.

Same tail every time. The integer part keeps changing because the prime keeps changing. The tail does not. After the very first division line, the algorithm forgets which prime it started from and only remembers the remainder. The remainder is $3$ at every prime ending in $3$. From the second line on, the chain of divisions is the *same chain*, regardless of which prime we walked in with.

That is why the tail depends only on the last digit, and that is the part I find genuinely beautiful about this picture. The prime gives up everything except its last digit on the very first line of the Euclidean algorithm, and from there the continued fraction is the same continued fraction that any other prime in the same family would have produced. The last digit is not a label. It is the entire surviving signal of the prime, as far as the continued fraction is concerned.

Run the algorithm on a prime ending in $1$, like $11$ or $31$ or $41$, and the tail is $[10]$. A single integer, no recursion, the algorithm bottoms out on its second line. Run it on a prime ending in $7$, like $17$ or $37$ or $47$, and the tail is $[1, 2, 3]$. Three steps of recursion, the deepest of the four. Run it on a prime ending in $9$, like $19$ or $29$ or $59$, and the tail is $[1, 9]$. Two steps, but with one big jump at the end.

Here are the four tails of base ten side by side, with what each one tells you about the prime's bin distribution.

```
last digit r   continued fraction tail   number of "large" bins
-------------  -----------------------  -----------------------
    1                  [10]                       0
    3                  [3, 3]                     2
    7                  [1, 2, 3]                  6
    9                  [1, 9]                     8
```

The "large bins" column is the count of digit positions in $1/p$ that are oversized, the bins where the digit function lands more residues than average. Primes ending in $1$ have a perfectly uniform bin distribution. Primes ending in $3$ have two oversized bins. Primes ending in $7$ have six. Primes ending in $9$ have eight.

The pattern is unmistakable. The number of large bins is exactly $r - 1$. Primes ending in $1$ are uniform because the tail $[10]$ is trivial, no recursion at all. Primes ending in $9$ are maximally unbalanced because the tail $[1, 9]$ ends in the deepest jump. The continued fraction is sorting primes by structural complexity, and it is doing it using nothing but the last digit.

Picture the four tails as four different stamps pressed into the integers. Every prime arrives at the digit function already wearing one of the four stamps. The stamp tells you in advance how the prime's loop will respond to shifting, before you have computed a single digit of $1/p$. You can do the stamping yourself, on any prime, in five lines of arithmetic with a pencil. That part is yours to take with you.

## The Moiré picture

The table answered the question of *what* the four families look like, but it left a deeper question open. Why does the continued fraction know how the loop will respond to shifting? What is the continued fraction *doing*? I sat with the table for a long time before the right metaphor walked up and tapped me on the shoulder.

You have seen the effect before, even if you never had a name for it. Hold two combs up against each other and tilt one slightly. The teeth on each comb are evenly spaced, but where the two sets of teeth overlap you see a slow band rolling across the combs from one side to the other, much wider than any individual tooth, sliding as you tilt. Photograph a striped shirt on a television and the camera invents wavy bars that crawl across the fabric and make your eyes feel slightly seasick. Drive past a chain-link fence with another fence behind it and watch the slow dark ripples race along the back fence as you move. The phenomenon has a name. It is called a *Moiré pattern*, after the French silk whose weave displays the same kind of slow interference bands when light crosses it twice.

Now do it with primes. Picture one set of marks spaced exactly $b$ apart and a second set spaced exactly $p$ apart, both running off down the same line out to infinity. Where the two sets nearly coincide you get broad quiet bands, almost-meeting after almost-meeting. Where they fall out of step the pattern bristles with structure. Two unbelievably simple grids, two integers, and between them a Moiré that is anything but simple. And here is the surprise. The continued fraction of $p/b$ is exactly the mathematical object that records how the two grids interfere at every resolution scale. The partial quotients of the continued fraction are the *layers* of the Moiré, the broadest band at the top of the list and the finest interference at the bottom. The Euclidean algorithm I had you running with a pencil a moment ago was peeling the Moiré apart layer by layer the whole time, and you did not know that was what you were doing.

A large partial quotient, like the $10$ at the top of the $r = 1$ tail, means the two grids are nearly in alignment at that scale, and the Moiré is broad and quiet. The autocorrelation is flat. A bunch of small partial quotients, like the $1, 2, 3$ in the $r = 7$ tail, means the grids are misaligned at every scale, and the Moiré is crowded with structure at every resolution. The autocorrelation is rich.

The spectral gate, in this picture, is the resolution geometry of the Moiré pattern between the prime and the base. It is not exotic. It is what you get when you pay attention to which parts of the prime's grid interact with which parts of the base's grid.

## How many families are there

Four families is suspiciously small. The natural question is whether four is special to base $10$, or whether every base has its own modest count. The answer is the second, and the count is the cleanest thing in the paper.

**Theorem (informal).** *In base $b$, there are exactly $\varphi(b)$ spectral families, where $\varphi$ is Euler's totient function (the number of integers between $1$ and $b$ that are coprime to $b$).*

In base $10$, $\varphi(10) = 4$. The four families are $r \in \{1, 3, 7, 9\}$. In base $12$, $\varphi(12) = 4$. The four families are $r \in \{1, 5, 7, 11\}$. In base $30$, $\varphi(30) = 8$. Eight families. In a prime base $b = q$ (where $q$ is prime), every nonzero residue is coprime, so $\varphi(q) = q - 1$ and you get $q - 1$ families.

This is the seed of an idea I want to take much further. If primes end up sorted into a small finite number of families by their last digit, with each family having its own structural signature, then the digit function is doing more than producing decimal expansions. It is sorting the primes into a classification scheme that nobody had a name for before. Last digit gives me $\varphi(b)$ families. What if I went deeper? What if last *two* digits gave me a finer classification, last *three* digits a finer one still? The four families in base $10$ at depth one might be the bottom rung of a ladder I can climb.

## A speculation I want to chase

There is a thread running through all of this that I cannot stop pulling on. I will lay it out and you can decide for yourself whether it is real or a mirage.

The chain that connects classical Ramanujan sums to the Riemann zeta function goes through a Dirichlet series, summing the harmonics over all moduli. If my filtered version is a real generalization, there might be a parallel object, a *structural* Dirichlet series that sums my filtered Ramanujan sums over all primes. Whether it has a meromorphic continuation, whether it has a functional equation, whether it relates to the family of Dirichlet $L$-functions modulo $b$, I do not know yet. The series is defined only for the primes where the base generates the full multiplicative structure, and even there I have not pinned down its analytic behavior. But the family decomposition into $\varphi(b)$ classes is exactly the shape that Dirichlet $L$-functions have, one $L$-function per character mod $b$, and the resemblance is too clean to ignore. I want to know whether the analogy is structural or just suggestive. That is the route I am working on next.

## What is left to do

Every paper in this chain is half a result and half a list of things I have not yet figured out. This one is no different. Two pieces of the picture are not yet in place, and naming them is the only honest way to close out.

The first is that the cleanest version of the argument goes through only when the base $b$ generates the full multiplicative structure modulo $p$. At primes where it does not (the multi-coset primes), the same machinery needs an extra layer of harmonic analysis on top of the one used here, and I have not yet worked out what that layer should look like. I expect the family picture to survive intact at multi-coset primes, with a refined version of each family, but I have not proved it.

The second is the Dirichlet series speculation above. If there is a real connection to $L$-functions waiting in there, I want to find it. If the connection is fake, I want to know that too, so I can stop circling it.

## A note from 2026

*April 2026*

The four families from this paper turned out to be the seed of much larger pattern. The "spectral family" framing introduced here, the idea that primes are sorted by their last digit into a finite number of structurally distinct kinds, became one of the central organizing ideas of the alignment program. By the time of [the collision invariant](https://alexpetty.com/the-collision-invariant/) the "last digit" had grown into "the last two digits", and the four families in base $10$ at depth one had grown into forty fingerprints at depth two. The four families are the bottom rung of a ladder, and every prime carries the fingerprint of the rung it sits on. The ladder I speculated about in the body of this paper is real, and it has been climbed.

The phase-filtered Ramanujan sum framing also generalized. The general object is the collision invariant table from [the collision spectrum](https://alexpetty.com/the-collision-spectrum/), and the specific filter that shows up in this paper is the depth-one slice of that table. The continued fraction connection that I leaned on heavily here became less central later, replaced by a cleaner Fourier derivation that runs through Dirichlet characters. The conclusion was the same. The continued fraction tail of $p/b$ and the depth-one row of the collision invariant table are the same object viewed two ways.

The Dirichlet series speculation at the end of the body turned out to be real, and it is the reason this paper matters in retrospect. The "structural Ramanujan sum" $c_p^G(\ell)$ I defined in the closing section did decompose over Dirichlet characters mod $b$, and the decomposition fed straight into the Parseval moment identity in [the collision spectrum](https://alexpetty.com/the-collision-spectrum/). The four-family decomposition from this paper became the four-character decomposition of $L(s, \chi)$ for $\chi$ modulo $10$. The analogy I called "too clean to ignore" was the right instinct.

The "spectral gate" name did not survive into later work. I started calling the same object "the bin geometry" or "the character sum factor" once I had a better picture of what it was doing. But the picture from this paper, of harmonics passing or being blocked depending on which family the prime sits in, is exactly what the decomposition theorem in the collision spectrum makes precise. Every Fourier coefficient of the collision invariant factors into an L-function part and a family part. The family part is the gate from this paper, generalized.

It is also worth saying that the all-zero pattern at $p = 7$ that drove [the autocorrelation formula](https://alexpetty.com/the-autocorrelation-formula/) was not a coincidence. At $p = 7$ in base $10$ the loop length is six and the gate width is nine, so the gate is wider than the loop. There is no room for any non-deranging shift, and every nontrivial shift is forced to be deranging. $p = 7$ is the smallest prime where the gate completely covers the loop. The primes where the structure feels mysterious at small scale are exactly the primes where there is too little room left for any signal at all. Once the prime grows past the gate width, the signal returns and the family fingerprint becomes visible.

.:.

---

## Try it yourself

```
$ ./nfield gate 7
  family: r = 7, gate width 9
  loop length 6 (smaller than the gate)
  every nontrivial shift is deranging, R(ell) = 0 for all ell > 0

$ ./nfield gate 29
  family: r = 9, gate width 9
  loop length 28
  19 shifts carry signal, 9 vanish
  large bins: 8 (matches r - 1)

$ ./nfield gate 41
  family: r = 1, gate width 9
  loop length 5 (smaller than the gate)
  large bins: 0 (uniform, matches r - 1)

$ ./nfield gate 53
  family: r = 3, gate width 9
  loop length 13
  large bins: 2 (matches r - 1)
  same gate as 13, 23, 43, 73, every prime ending in 3
```

Four primes, four families, the loop sometimes smaller and sometimes larger than the gate, and in every case the number of large bins equals $r - 1$. Pick any prime, run the same command, and watch which of the four families it falls into.

Code: [github.com/alexspetty/nfield](https://github.com/alexspetty/nfield)
Paper: [Phase-Filtered Ramanujan Sums and the Spectral Gate](https://github.com/alexspetty/nfield/blob/main/research/phase_filtered_ramanujan.pdf)

---

*Alexander S. Petty*
April 2022 (updated April 2026)
.:.
