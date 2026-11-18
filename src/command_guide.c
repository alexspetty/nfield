#include <stdio.h>
#include <string.h>
#include "command_guide.h"
#include "verification_routes.h"

#include "command_actions.inc"

static const NfieldCommandGuide guides[] = {
    {"analyze",
     "research",
     "Choose denominators worth studying before opening their complete digit fields.",
     "Denominator n and digit base.",
     "Period, reference alignment and the field invariants in one summary.",
     "nfield analyze 7 --base 10",
     "Compare summaries, then use field for the words or decompose for the signed residual.",
     "The summary includes numerical values; use the corresponding exact operation when an exact rational is needed."},
    {"field",
     "research",
     "Inspect the actual repeating words of all fractions with your chosen denominator.",
     "Denominator n and digit base.",
     "A row for each proper fraction, with its terminating or repeating expansion.",
     "nfield field 7",
     "Change --base to compare the same rational field across digit systems; use div for the corresponding long-division steps.",
     "The displayed field grows with its denominator and period; start with a modest n."},
    {"reset-forest",
     "research",
     "Measure how a chosen reset family and its complement contribute to one sampling defect.",
     "Prime-square work/source: odd prime p and divisor or return window. General project: cutoff N, signed rational weights, a modulus/divisor/mask and optional grid.",
     "Exact rational energies, selected/complementary work, complete mixed terms, contact, curvature, reset masses and source coefficients.",
     "nfield reset-forest 31 --returns 3 --json",
     "Compare --divisor choices, inspect source for the prime-square collapse map, or use project for your own weighted source. Export --json or --csv for further calculations.",
     "Prime-square work/source accepts odd primes 3..251; project accepts N=0..64. Every reset reads the complete source. Finite values do not establish the open uniform complementary bound."},
    {"native-refinement",
     "research",
     "Price a change of sampling or test how much of a response a chosen detector can capture.",
     "Detector size, clock pair, transport size, divisor family or supplied rational response bounds.",
     "Gram data, signed pairings, projection costs and exact or enclosed quantities for the selected action.",
     "nfield native-refinement kernel 2 3",
     "Use kernel to inspect a pair before detector/transport; trace retains every old row and can write a new JSON result.",
     "Input caps differ by action. Some projections are numerical; a computed gain does not prove the remaining uniform lower bound."},
    {"align",
     "research",
     "Compare a fractional field with its synchronized reference word.",
     "Denominator n and digit base.",
     "The synchronized reference-alignment score for that field.",
     "nfield align 7 --base 10",
     "Compare bases or denominators; use coherence-decomposition when the pairwise score and signed difference are also needed.",
     "The short command prints a decimal score. Reference and pairwise alignment have different sample spaces."},
    {"field-observation",
     "research",
     "Experiment with your own finite fields, endpoint readings, sampling grids and observation weights.",
     "Comma-separated rational or complex component data, grid size, shift and optional matrix request.",
     "Continuous and sampled work, their defect, and component/mixed matrices where supported.",
     "nfield field-observation clocks 25 0 1,2 0,0 1,1 --matrix",
     "Choose clocks, pulses, harmonics or segments; vary the observation while keeping the same source inputs.",
     "Lists must match. Endpoint readings and cross terms are part of the input; finite identities do not supply uniform limit estimates."},
    {"div",
     "research",
     "Inspect the long-division steps that produce a digit field.",
     "Denominator n and digit base.",
     "The division table connecting each remainder to its emitted digit and next remainder.",
     "nfield div 7 --base 10",
     "Use it to explain a word from field or compare the same fraction in another base.",
     "Requires n>=2; large denominators produce large tables."},
    {"decompose",
     "research",
     "Separate reference alignment from mutual alignment inside the same field.",
     "Denominator n and digit base.",
     "Alpha, pairwise sigma and the signed residual F=alpha-sigma.",
     "nfield decompose 13 --base 10",
     "Compare denominators or bases, then use coherence-decomposition pairs to locate the contributing pairs.",
     "Pairwise alignment requires at least two proper fractions; the residual can have either sign."},
    {"polar",
     "research",
     "Inspect digit words alongside their cumulative polarity coordinates.",
     "Denominator n and digit base.",
     "The closed digit field, cumulative orientation and accumulated digit-phase rows.",
     "nfield polar 7 --base 10",
     "Use analyze for a scalar summary, then compare polar output across related denominators.",
     "These are finite field diagnostics; coordinate patterns alone do not imply a uniform law."},
    {"survey",
     "research",
     "Find trends or exceptional denominators over an initial range.",
     "Maximum denominator, base and optional CSV format.",
     "One row of field invariants for each surveyed denominator.",
     "nfield survey 20 --base 10 --csv",
     "Export rows for plotting, then investigate selected denominators with field or decompose.",
     "Runtime grows with the number and periods of denominators; use range to restrict a later scan."},
    {"range",
     "research",
     "Compare field invariants over a specific interval rather than restarting at the first denominator.",
     "Minimum and maximum denominators, base and optional CSV format.",
     "Rows of field invariants over the requested interval.",
     "nfield range 10 20 --base 10 --csv",
     "Use adjacent intervals to extend a survey and retain machine-readable rows.",
     "A finite trend is evidence about the requested interval, not a limiting estimate."},
    {"table",
     "research",
     "Inspect the collision-deviation table for a chosen digit base.",
     "Base, supplied positionally or with --base, and optional --pairs.",
     "Finite residue-class collision values and optional reflected pairs.",
     "nfield table 5 --pairs",
     "Look for a residue pattern, then use collision-table inspect or finite-determination on a particular integer.",
     "The table is periodic in the stated finite modulus; prime-frequency behavior requires a separate calculation."},
    {"spectral",
     "research",
     "Find which additive frequencies carry digit-bin agreement for a prime field.",
     "Prime modulus and digit base.",
     "Digit-bin Fourier power and its finite spectral summary.",
     "nfield spectral 13 --base 10",
     "Use spectral-power overlap for interval overlap data; use spectral-structure for multiplicative orbit frequencies.",
     "Additive and multiplicative spectra are different coordinates. Fourier values are numerical with the stated residuals."},
    {"equations",
     "reference",
     "Look up the definitions behind the quantities printed by the field commands.",
     "No numerical inputs.",
     "A reference sheet of the principal invariants and relations.",
     "nfield equations",
     "Use beside analyze, align or decompose when checking a symbol or normalization.",
     "This is mathematical reference help, not an execution or verification result."},
    {"tables",
     "reference",
     "Locate the registered fixed reference tables.",
     "An optional registered table name.",
     "A list of available tables or the requested reference rows.",
     "nfield tables",
     "Use the associated mathematical family for calculations on your own parameters.",
     "This compatibility entry uses fixed fixtures rather than an arbitrary-input calculation."},
    {"verify",
     "verification",
     "Check implementations against their declared mathematical contracts.",
     "A named C check family and optional check; families lists the available names.",
     "Executed checks, tested finite domains and assertion outcomes.",
     "nfield verify reset-forest",
     "Use families to find a check, then run that named family. Use reset-forest contracts --json for a structured report of the source and forest checks.",
     "These C checks run without Lean or proof sources. A finite PASS applies only to executed assertions; formal proofs remain in the separate proof project."},
    {"daemon",
     "service",
     "Use nfield calculations from another local program through its JSON/TCP service.",
     "Listening port and worker count.",
     "The same command output and status returned in a JSON response.",
     "nfield daemon --port 9090 --threads 4",
     "Send one JSON request per connection; ordinary mathematical commands use the same executable dispatch.",
     "This existing service is JSON/TCP, not HTTP. Shell operators and quoted shell expressions are not command syntax."},
    {"completion",
     "navigation",
     "Discover commands, actions and supported flags while typing in a shell.",
     "Shell name bash, zsh or fish.",
     "A shell completion script.",
     "nfield completion bash",
     "Load the emitted script using the installation line below; Tab then discovers current names and options.",
     "Completion suggests syntax; numerical domain validation occurs when the command runs."},
    {"version",
     "navigation",
     "Record which nfield executable produced a result.",
     "No numerical inputs.",
     "The build version derived from link time.",
     "nfield version",
     "Save the version with input parameters when comparing results across builds.",
     "A version identifies the build; it is not a theorem or coverage certificate."},
    {"commands",
     "navigation",
     "Choose a tool by its research purpose before reading its full syntax.",
     "Optional search terms; --examples shows runnable starts and --json returns the catalog.",
     "Matching command purposes and optional examples, or structured action contracts.",
     "nfield commands spectrum --examples",
     "Search by a quantity or task, then use nfield help <name> <action> for its complete input contract. Multiple terms must all match; search ignores letter case.",
     "The catalog describes interfaces, not computed results. Format support belongs to individual actions."},
    {"help",
     "navigation",
     "Find the purpose, inputs, output and syntax of an nfield command.",
     "A command or help topic.",
     "Research guidance followed by the detailed usage and domain notes.",
     "nfield help reset-forest",
     "Use commands to discover a family, help to understand it, and completion to enter its arguments.",
     "Help describes a calculation; it does not execute that calculation."},
    {"reciprocal-square-selection",
     "research",
     "Compare exact alignment with the reciprocal-golden threshold for your prime and supported multiplier.",
     "Prime p, supported multiplier m, base, or a prime scan limit.",
     "Exact alignment, rational threshold comparison and cubic factor/remainder information.",
     "nfield reciprocal-square-selection inspect 3 4 --base 10",
     "Use inspect for a field, cubic for its polynomial, and scan to compare the prime parameter.",
     "The alignment formula requires its one-digit support hypotheses; the fixed table is a reference fixture."},
    {"weighted-reference-profile",
     "research",
     "Change the weight of a reference population and study the resulting alignment or branch.",
     "Integer modulus, supported multiplier, rational weight and base; branch/order parameters for other actions.",
     "Exact weighted scores, quadratic-field coordinates and finite substitution counts.",
     "nfield weighted-reference-profile inspect 3 4 1 1 --base 10",
     "Compare inspect at several weights; use branch or reflection-product to examine the associated projective map.",
     "Supported blocks and congruence assumptions are checked. Torsion and transport fixtures belong to focused verification."},
    {"digit-partition",
     "research",
     "Determine how base-supported and coprime factors organize a fractional field.",
     "Denominator, base and optional synchronized depth.",
     "Support split, clearing depth, digit-bin populations and synchronized alignment.",
     "nfield digit-partition inspect 6 --base 2",
     "Start with a composite denominator; change the base to see which factors move into the supported part.",
     "The requested depth must admit the synchronized construction; printed fixed tables are examples."},
    {"alignment-limit",
     "research",
     "Measure the orbit/coset correction to alignment for a prime core and supported multiplier.",
     "Prime, multiplier, base and optional depth or scan limit.",
     "Coset data, finite alignment and limiting comparison for the specified inputs.",
     "nfield alignment-limit inspect 3 4 --base 10",
     "Inspect one case, use cosets to resolve its correction, then table to compare eligible primes.",
     "The limit formula retains its prime-core/support hypotheses; a finite scan is not a new limit proof."},
    {"three-tier",
     "research",
     "Classify how a denominator behaves after its supported factors are removed.",
     "Denominator or maximum denominator, base and optional depth.",
     "Tier, rough/support split and alignment values for requested finite cases.",
     "nfield three-tier classify 30 --base 10",
     "Use classify to locate a tier, inspect a representative, and scan to compare its range.",
     "Composite rough parts have their own domain and signed behavior; do not apply a prime-core formula indiscriminately."},
    {"deficit-lattice",
     "research",
     "Construct exact alignment-deficit ratios and compare arithmetic tuning intervals.",
     "Prime, supported multiplier or pair of multipliers, base and scale factor.",
     "Exact deficit values, ratios and supported scale tables.",
     "nfield deficit-lattice inspect 3 4 --base 10",
     "Use inspect to establish a value, ratio to compare two fields, then the scale actions for musical interval tables.",
     "Support conditions and common scaling matter; scale examples are specified constructions."},
    {"coherence-decomposition",
     "research",
     "Find whether a field statistic comes from its reference word or from agreements between its fractions.",
     "Denominator, prime/support factors, base and synchronized depth.",
     "Exact alpha, sigma, signed F and optionally every nonzero unordered pair score.",
     "nfield coherence-decomposition pairs 13 --base 10",
     "Inspect the aggregate, then use pairs to identify the contributing word pairs.",
     "Alpha and sigma average different sample spaces. Their difference remains signed."},
    {"cross-alignment",
     "research",
     "Retain every pairwise agreement when a single mean hides the structure of a field.",
     "Denominator or prime, base and synchronized depth.",
     "Cross-alignment matrix, orbit blocks and finite Fourier decomposition.",
     "nfield cross-alignment matrix 7 --base 10",
     "Inspect matrix first, then prime/fourier/block for compatible structural coordinates.",
     "Matrix size grows with the field; numerical spectral calculations retain the stated tolerance."},
    {"spectral-structure",
     "research",
     "Find rank, null directions and frequency fibers in a prime field's alignment matrix.",
     "Prime modulus and digit base.",
     "Orbit words, occupied bins, fiber ranks and multiplicative character energies.",
     "nfield spectral-structure inspect 7 --base 2",
     "Compare inspect with two-coset where eligible; use character to resolve the multiplicative frequencies.",
     "Fourier ranks and spectra are numerical at the reported tolerance. These are not Dirichlet L-values."},
    {"spectral-power",
     "research",
     "Inspect how digit intervals distribute additive Fourier power and overlap.",
     "Prime modulus and digit base.",
     "Digit-bin powers, interval kernels and overlap profiles.",
     "nfield spectral-power overlap 13 --base 10",
     "Use inspect for the spectrum and overlap to explain it from finite bin intersections.",
     "Finite counts are exact; Fourier values use the reported numerical convention."},
    {"autocorrelation",
     "research",
     "Compare a digit field with its additive shifts or multiplicative slices.",
     "Prime, base and optional shift/multiplier or orbit coset.",
     "Same-bin cross-spectrum, correlations and orbit harmonics.",
     "nfield autocorrelation slice 13 2 --base 10",
     "Use inspect for the full profile, slice for one multiplier, and orbit for a multiplicative family.",
     "Additive displacement and multiplicative multiplier are distinct inputs; numerical transforms are finite."},
    {"phase-gate",
     "research",
     "Locate phase and multiplier combinations that admit or suppress digit collisions.",
     "Prime, multiplier, base or a chosen bin-word action.",
     "Ramanujan selectors, phase-gate data and finite multiplier/cell structure.",
     "nfield phase-gate inspect 13 2 --base 10",
     "Inspect one multiplier, then compare the complete multipliers or bin-word output.",
     "Use the printed prime/base hypotheses; zero gates describe finite collisions, not prime-pair existence."},
    {"bin-derangements",
     "research",
     "Find multipliers that move every residue out of its original digit bin.",
     "Prime modulus and digit base.",
     "The zero-collision family, counts, constructive mean and selected lag data.",
     "nfield bin-derangements family 13 --base 10",
     "Use family to obtain the multipliers, inspect for their counts, and mean for the complementary population.",
     "The base/prime domain controls the gate formula; a zero multiplier collision is not a primality claim."},
    {"collision-characters",
     "research",
     "Decompose your finite prime-weighted collision sum into residue and character channels.",
     "Cutoff or prime, base, lag and complex exponent.",
     "Exact collision deviations plus numerical channel sums, transforms and reconstruction residuals.",
     "nfield collision-characters inspect 1000 --base 5 --lag 1",
     "Inspect a finite cutoff, vary it to compare channels, and use prime for a single exact deviation.",
     "Character transforms are numerical. Finite cutoff behavior does not establish convergence."},
    {"silent-primes",
     "research",
     "Find primes with zero prescribed digit collision and inspect their variance.",
     "Prime or base, lag, and the recipe/variance action.",
     "Silence candidates, exact collision values and variance components.",
     "nfield silent-primes prime 13 --base 10 --lag 1",
     "Use recipe to enumerate the specified candidate mechanism, prime to inspect one case, and variance to compare nonzero behavior.",
     "Silence concerns a digit statistic at the selected lag; it does not remove the prime from other statistics."},
    {"collision-fluctuation",
     "research",
     "Measure a prime's collision deviation and compare it with its residue class.",
     "Prime, base or requested table/class action.",
     "Finite deviations, class means and prime-weighted finite sums.",
     "nfield collision-fluctuation prime 13 --base 10",
     "Start with prime; table and classes expose the periodic baseline before interpreting a sum.",
     "Fixed snapshots are verification fixtures. Finite fluctuations do not supply an infinite asymptotic."},
    {"collision-centering",
     "research",
     "Remove the predictable fiber bias from a collision value before comparing residuals.",
     "Integer, base, lag or a finite sum cutoff.",
     "Direct and centered collision values, fiber means and centered prime sums.",
     "nfield collision-centering inspect 113 --base 10 --lag 1",
     "Inspect one value, use fibers to see its baseline, then sum to study the remaining finite fluctuations.",
     "Centering uses the whole reduction fiber, not a fitted mean from the chosen prime sample."},
    {"collision-table",
     "research",
     "Compare integers through the exact periodic collision table they share.",
     "Integer or pair of integers, digit base and requested table view.",
     "Residue labels, collision values, reflected pairs, extrema and table summaries.",
     "nfield collision-table compare 13 113 --base 10",
     "Use compare to test a suspected periodic relation; table exposes every unit class.",
     "Residue-table equality does not imply the represented integers share other arithmetic properties."},
    {"collision-transform",
     "research",
     "Study the character support that survives centering and compare a specified prime interval.",
     "Integer or interval, base, lag and optional real exponent.",
     "Centered values, support/conductors, finite spectrum and prime-window sums.",
     "nfield collision-transform window 100 1000 --base 5 --lag 1",
     "Inspect the table and gate first; spectrum identifies channels, then window evaluates the same centered object on primes.",
     "Spectra are numerical; table and window size limits are separate. No critical-strip estimate follows from a finite window."},
    {"residue-three-neutrality",
     "research",
     "Separate true residue-three contributions from the residue labels inside a digit table.",
     "Integer or prime interval, base, lag and optional exponent.",
     "Quotient carry, lifted channel sums and the nontrivial modulo-three twist.",
     "nfield residue-three-neutrality inspect 113 --base 10 --lag 1",
     "Use inspect to see the quotient shift, channels for the full lift, then split for a finite prime interval.",
     "An internal table slice is not automatically the same as the represented integer's true residue class."},
    {"compatible-residue-channels",
     "research",
     "Resolve collision data into true prime or squarefree residue channels.",
     "Integer, channel prime or squarefree modulus, base, lag and finite cutoff.",
     "Reconstructed true residues, lifted channel sums and finite character statistics.",
     "nfield compatible-residue-channels channels 3 --base 5 --lag 1",
     "Compare internal and true channels; simultaneous joins several compatible prime channels in one modulus.",
     "Exact channel identities and numerical finite correlations have separate scope; cutoff-uniform behavior remains separate."},
    {"centered-collision-table",
     "research",
     "Obtain an exact centered value or complete centered table at a specified lag.",
     "Base, lag and optional unit residue.",
     "Rational centered values, reflections and reduction-fiber sums.",
     "nfield centered-collision-table inspect 5 1 7",
     "Use inspect for values at your selected residue; verify centered-collision-table complete checks the full finite table.",
     "Only supported finite moduli are admitted; centered class data do not count prime occurrences."},
    {"finite-character-pairing",
     "research",
     "Measure character pairing in a finite prime window for your chosen base and lag.",
     "Base, lag and prime cutoff.",
     "Pairing, channel energies, correlations and direct-sum comparison at that cutoff.",
     "nfield finite-character-pairing one 3 1 --cutoff 1000",
     "Change --cutoff on the same base/lag before comparing different tables.",
     "Long-double numerical data at sigma=1/2; a trend is not a cutoff-uniform bound."},
    {"coprime-base-orthogonality",
     "research",
     "Measure cross-work between two centered digit tables, including shared-factor cases.",
     "Two bases and their lags.",
     "Exact cross term, table energies, common-quotient data and recovery/splitting values.",
     "nfield coprime-base-orthogonality pair 3 1 5 1",
     "Use pair for coprime bases; common-quotient explains what survives when the bases share factors.",
     "Choose domains small enough for the finite tables. Coprime zero work is not assumed for a shared-factor pair."},
    {"natural-prime-sum-window",
     "research",
     "Compare several bases on equal prime windows without mixing their lower boundaries.",
     "Explicit upper cutoff and, for common-tail, a common lower endpoint.",
     "Per-base finite sums, combined values and summation-order residuals.",
     "nfield natural-prime-sum-window common-tail --lower 997 --cutoff 2000",
     "Contrast common-tail with base-boundaries to see the contribution of unequal starting points.",
     "The base set is fixed by this operation; the endpoints are adjustable. Sums are numerical and finite."},
    {"primitive-odd-sector",
     "research",
     "Measure how a prime-base collision spectrum occupies its primitive odd character sector.",
     "Odd prime base and finite prime cutoff.",
     "Character counts, pair energies, relabeling variance, displacement and entropy support.",
     "nfield primitive-odd-sector inspect 5 --cutoff 1000",
     "Compare the same base at several cutoffs or different bases at the same cutoff.",
     "Finite energy/correlation data do not establish a limiting overlap or repulsion constant."},
    {"conjugate-pair-relabeling",
     "verification",
     "Recheck the recorded finite relabeling law and reference character data.",
     "A registered fixed check; arbitrary populations are not accepted by this family.",
     "Mean/variance fixture checks and fixed cutoff reference results.",
     "nfield verify conjugate-pair-relabeling",
     "For adjustable base and cutoff diagnostics, use primitive-odd-sector inspect.",
     "This family is verification, not a user-supplied relabeling operation."},
    {"additive-reflection-well",
     "research",
     "Locate the negative reflection well and compensating mass of a centered digit table.",
     "Digit base.",
     "Full cyclic convolution, exact well/compensation values and finite Fourier square.",
     "nfield additive-reflection-well inspect 5",
     "Compare bases while retaining the complete convolution, rather than only its most negative entry.",
     "Integer convolution values are exact; Fourier corroboration is numerical."},
    {"reflected-prime-pair-sign",
     "research",
     "Evaluate centered-table weights on every prime pair in a chosen finite even-target range.",
     "Base and maximum even target.",
     "Target sums, pair counts and signed square-sum comparisons.",
     "nfield reflected-prime-pair-sign sweep 3 --max-even 100",
     "Increase the target range for a fixed base and inspect where the weighted contributions occur.",
     "Targets are multiples of b^2, with a finite maximum of 100000; these weights are not a proof of Goldbach or twin primes."},
    {"collision-spectrum-factorization",
     "research",
     "Resolve a collision coefficient into primitive character and Bernoulli factors.",
     "Odd prime base, primitive odd character index and optional unit multiplier.",
     "Direct coefficient, fiber cancellations and finite Bernoulli transform/factorization values.",
     "nfield collision-spectrum-factorization inspect 5 1",
     "Inspect a channel first; transform then tests its dependence on a selected multiplier.",
     "Supported odd prime bases through 127; numerical character values do not locate L-function zeros."},
    {"special-value-moment",
     "verification",
     "Recheck the fixed weighted L-value moment fixtures.",
     "A registered fixed verification action.",
     "Finite moment and Parseval check outcomes.",
     "nfield verify special-value-moment",
     "Use collision-spectrum-factorization or short-sum-bernoulli-correlation moments for adjustable character data.",
     "The fixed panel does not accept a user-selected moment population."},
    {"base-five-cyclotomic-identity",
     "verification",
     "Recheck the fixed base-five cyclotomic polynomial and fourth-moment identity.",
     "A registered fixed verification action.",
     "Exact polynomial and moment check outcomes.",
     "nfield verify base-five-cyclotomic-identity",
     "Use spectral or collision-spectrum-factorization for adjustable finite spectral calculations.",
     "This is a specified identity check, not a general cyclotomic algebra calculator."},
    {"weighted-remainder-state",
     "research",
     "Build and compare finite weighted clock states, boundary work and distribution data.",
     "Resolution, cutoff and action-specific rational phases, weights, moduli or intervals.",
     "Exact state/mass/kernel quantities or explicitly numerical/enclosed spectra and finite laws.",
     "nfield weighted-remainder-state inspect 8 16",
     "Start with inspect, boundary or conductor; use clock/finite-weights for custom clock data, and pairing/gram for signed work. Detailed actions below cover transforms, distributions and inversion.",
     "This large family has action-specific limits and arithmetic conventions. Infinite laws and uniform estimates are distinct from a finite evaluation."},
    {"capacity-resolution",
     "research",
     "Measure how capacity changes with integer resolution and the observation window.",
     "Resolution and truncation, dyadic window, progression or sample count.",
     "Capacity, diagonal/residual terms, boundary corrections and finite conditional means.",
     "nfield capacity-resolution inspect 30 60",
     "Inspect one resolution, then use sample for CSV over a window or progression to condition by residue class.",
     "Long-double numerical evaluations. Prime observations use continuous capacity at p-1, not finite digit-grid energy."},
    {"capacity-generation",
     "research",
     "Construct capacity from explicit digit sources, carry cells and finite recovery data.",
     "Source base/lag, carry residues, rational amplitudes, finite cutoff or profile coefficients.",
     "Exact source rows, carry covariance, recovered weights, rational bounds and profile values.",
     "nfield capacity-generation source 3 1",
     "Build a source, inspect its carry response, then ledger/refine to examine how primitive weights are assembled.",
     "Limits and positivity hypotheses differ by action. A raw profile is not automatically positive or normalized."},
    {"collision-sampling",
     "research",
     "Compare continuous collision work with a specified finite sampler and resolve its error by carriers.",
     "Odd prime or source cutoff, sampling grid/shift, carrier and explicit finite prefixes.",
     "Exact capacity, sampled work, contact and carrier decompositions; selected transforms are numerical.",
     "nfield collision-sampling inspect 7",
     "Inspect the defect first; carrier and prefix localize contributions, grid changes the observation, and source/decomposition retain the original source.",
     "Most prime operations use 3..251. The sampled action has a larger domain with numerical capacity; finite output does not prove the global rate."},
    {"boundary-spectrum",
     "research",
     "Transform a boundary or weighted cell rule on a complete finite unit group.",
     "Modulus and selected cells or signed/complex cell weights; optional character index.",
     "Character phases, conductors, transformed values, energies and factorization residuals.",
     "nfield boundary-spectrum inspect 9 --support 0,4,8",
     "Use inspect for the full transform and channel to examine a selected CRT-indexed character.",
     "Moduli 2..512, including noncyclic unit groups. Complex transforms are numerical; not every composite modulus has a prime-power flux factorization."},
    {"short-sum-bernoulli-correlation",
     "research",
     "Compare finite short sums with Bernoulli character values at your chosen prime base.",
     "Odd prime base for moments.",
     "Normalized moments, the twist at two and variance from finite Bernoulli sums.",
     "nfield short-sum-bernoulli-correlation moments 5",
     "Repeat moments across supported bases; use the separate ledger check for the recorded reference rows.",
     "Odd prime bases 5..127; finite character moments do not establish their limiting correlation."},
    {"primitive-character-cancellation",
     "research",
     "Inspect which lower congruence fibers cancel for a chosen primitive odd character.",
     "Base, lag and character index in the documented prime-power coordinates.",
     "Rows of character, depth, residue, fiber size and complex sum, followed by cancellation residuals.",
     "nfield primitive-character-cancellation inspect 3 1 1",
     "Choose one character and examine all its lower fibers before comparing another conductor.",
     "Membership is exact; complex character sums use long-double roots of unity."},
    {"periodic-zeta-factorization",
     "research",
     "Evaluate a finite periodic-zeta collision model at a chosen complex argument.",
     "Base, lag, primitive odd character index, real part and imaginary part.",
     "Unit/nonunit sums, centered transform, factorized values and residuals.",
     "nfield periodic-zeta-factorization inspect 3 1 1 --sigma 0.5 --tau 0",
     "Vary sigma or tau on the same channel, keeping the finite model and numerical error report together.",
     "Base^(lag+1)<=4096; Lanczos/Euler-Maclaurin values are numerical, with no zero-location or uniform estimate certified."},
    {"collision-boundary-recovery",
     "research",
     "Recover a collision coefficient from a character boundary reading and compare the two boundary orientations.",
     "Base, lag and primitive odd character index.",
     "Direct left/right transforms, Bernoulli/Gauss expressions and eligible collision recovery.",
     "nfield collision-boundary-recovery inspect 3 1 1",
     "Use one channel to compare the left and right readings before combining them with an active-channel classification.",
     "Base^(lag+1)<=4096. Logarithms, cotangents and roots of unity are numerical."},
    {"active-collision-channel",
     "research",
     "Determine whether a character channel is visible to the chosen collision boundary.",
     "Base, lag and character index, or a census over the eligible characters.",
     "Finite diagonal boundary and active/inactive classification.",
     "nfield active-collision-channel census 3 1",
     "Use census to find channels, then inspect a specific index and examine its factorization.",
     "The finite visibility gate does not search for or certify L-function zeros."},
    {"collision-coordinate",
     "research",
     "Compute a multiplier's collision count from its exact coordinate and inspect zero-collision multipliers.",
     "Modulus or prime, multiplier and digit base.",
     "Coordinate, direct count, conjugation data and the rational zero family.",
     "nfield collision-coordinate inspect 13 2 --base 10",
     "Inspect one multiplier, gate for the full zero family, or conjugation for a composite coprime modulus.",
     "Prime coordinate formulas and composite conjugation have different domains; the command checks eligibility."},
    {"finite-determination",
     "research",
     "Reduce a large eligible integer's collision value to its finite residue class.",
     "Integer N, digit base and lag.",
     "Direct deviation, determining modulus, residue-table value and optional minimal-modulus witnesses.",
     "nfield finite-determination inspect 113 --base 10 --lag 1",
     "Compare integers differing by b^(lag+1); optimal shows witnesses against a smaller base power.",
     "N must be coprime to the base for this unit-table operation; all-prime-collision-label handles base primes separately."},
    {"reflection-identity",
     "research",
     "Inspect the complementary collision values at a reflected pair of residue classes.",
     "Residue, base and lag, or the complete table action.",
     "Exact reflected pair values, their sum and the complete-table mean.",
     "nfield reflection-identity inspect 13 --base 10 --lag 1",
     "Use inspect for one pair, then table to inspect all unit pairs in the same modulus.",
     "Reflection is in the specified finite modulus; endpoint conventions remain part of the identity."},
    {"half-group",
     "research",
     "Count the wrapping residues on either side of a chosen interior cut.",
     "Modulus and interior cut index.",
     "The wrapping count and its complement-bijection comparison.",
     "nfield half-group inspect 11 3",
     "Move the cut while holding the modulus fixed to inspect how the pairing changes.",
     "Only interior cuts in the admitted modulus domain are meaningful; endpoint cuts are excluded."},
    {"all-prime-collision-label",
     "research",
     "Assign a collision label to a prime even when it divides the digit base.",
     "Prime, base and lag.",
     "The direct label and either its unit-table coordinate or base-prime zero case.",
     "nfield all-prime-collision-label inspect 5 --base 10 --lag 1",
     "Compare a base prime with a coprime prime using the same base and lag.",
     "This labels the given prime; it does not predict which residue classes contain future primes."},
    {"finite-spectral-quotient",
     "research",
     "Compress a finite prime-label matrix while retaining its block action.",
     "Base, lag, number of primes and positive heat scale.",
     "Label populations, quotient matrix, bulk multiplicity, numerical modes and heat data.",
     "nfield finite-spectral-quotient inspect 3 --prime-count 30 --tau 1",
     "Compare prime populations at the same base, then inspect the quotient rather than building every matrix entry by hand.",
     "Label populations are exact; inverse kernels and spectral values are numerical with reported tolerance."},
    {"finite-prefix-slice",
     "research",
     "Measure how a custom digit-prefix support is seen by an arithmetic sampling phase.",
     "Denominator, base, prefix depth and selected cells.",
     "Exact support/carry counts, bulk and endpoint corrections, or transport-collapse data.",
     "nfield finite-prefix-slice inspect 11 --base 3 --depth 2 --support 0,4,8",
     "Use inspect for a coprime phase, all to retain nonunits, and collapse to separate the persistent quotient.",
     "b^N<=50000. The all action has a wider denominator domain than inspect/collision."},
    {"oriented-digit-comparison",
     "research",
     "Separate ascent, equality and descent in a two-digit reading.",
     "Base and phase, or prime and row with optional height.",
     "Signed digit response, ramified energy and reconstructed ascent/equality/descent counts.",
     "nfield oriented-digit-comparison inspect 5 5",
     "Compare unit and nonunit phases, then trichotomy to combine orientation with mass and collision counts.",
     "Orientation is sign(first digit-second digit); it is not an arbitrary digit-score function."},
    {"boundary-bernoulli-factorization",
     "research",
     "Resolve your prime-power cell support into visible boundary flux and conductor energies.",
     "Odd prime, depth, character exponent and selected support; correlation also takes two units.",
     "Boundary derivative, visible norm, Bernoulli transform, conductor energies and correlation data.",
     "nfield boundary-bernoulli-factorization inspect 3 2 1 --support 0,4,8",
     "Inspect a channel, use spectrum for all conductors, then correlation to compare selected unit shifts.",
     "Cyclic odd prime powers p^depth<=20000. Counts are exact; complex transforms and conductor energies use numerical arithmetic."},
    {"boundary-conductor-ledger",
     "research",
     "Find where the energy of a finite cell boundary sits among exact conductors.",
     "Modulus and indicator support, or base/depth for terminal collision support.",
     "Signed boundary, divisor pushdowns, primitive moments and exact conductor energies.",
     "nfield boundary-conductor-ledger inspect 9 --support 0,4,8",
     "Inspect a custom support and compare its proper pushdowns with the top-conductor contribution.",
     "Modulus 3..200000. CLI input is an indicator support; the library also supports bounded integer weights."},
    {"terminal-collision-conductor-ledger",
     "verification",
     "Recheck the fixed terminal-boundary conductor fixtures.",
     "A registered fixed audit.",
     "Exact prime-power and base-15 identity checks.",
     "nfield verify terminal-collision-conductor-ledger",
     "Use boundary-conductor-ledger inspect or terminal to choose your own support or base/depth.",
     "This panel is verification; the parameterized boundary-conductor-ledger is the research operation."},
    {"finite-state-orbit-boundary",
     "research",
     "Run your own digit-reading automaton along a remainder orbit.",
     "Base, modulus, state count, initial states and a transition table with accepting states or integer weights.",
     "Product orbit, transient, cycle, emitted-state readings and predecessor boundary.",
     "nfield finite-state-orbit-boundary inspect 2 7 2 1 0 --transition 0,1,1,0 --accepting 1",
     "Try parity first, then replace the transition table or state weights with a different finite digit rule.",
     "Coprime base/modulus, base<=64, states<=32 and modulus*states<=4096. A dynamical boundary differs from a full-residue additive boundary."},
    {"full-orbit-energy",
     "research",
     "Compute the boundary energy of a full prime-power remainder orbit.",
     "Base, odd prime and exponent.",
     "Multiplicative order, orbit support, thickness, conductor spectrum and exact total energy.",
     "nfield full-orbit-energy inspect 2 3 2",
     "Compare prime-power depths while retaining a base that generates the complete unit group.",
     "The base must be primitive at the requested prime power; coset energies do not follow from the full-orbit law."},
    {"quadratic-orbit-energy",
     "research",
     "Remove the resonant quadratic channel and measure the remaining subgroup energy.",
     "Odd prime.",
     "Quadratic subgroup, boundary, resonance and exact off-resonance energy.",
     "nfield quadratic-orbit-energy inspect 7",
     "Compare primes in different residue classes modulo eight.",
     "This is the index-two subgroup at prime modulus; higher-index subgroup energy uses a different calculation."},
    {"subgroup-jacobi-expansion",
     "research",
     "Resolve a subgroup boundary flux into quotient-character contributions.",
     "Prime modulus, subgroup generator and odd character exponent.",
     "Subgroup order/index, annihilator, resonance class, direct flux and Jacobi-type expansion.",
     "nfield subgroup-jacobi-expansion inspect 7 2 1",
     "Change the generator or character to compare resonance and off-resonance on the same prime field.",
     "Subgroup membership is exact; roots of unity and flux sums are numerical. No general higher-index closed energy law is implied."},
    {"prime-base-collision-energy",
     "research",
     "Compute collision energy and identify which finite carry or pole terms contribute.",
     "Odd prime digit base.",
     "Carry-table energy, exact Dedekind dictionary and diagonal/upper/lower pole masses.",
     "nfield prime-base-collision-energy inspect 5",
     "Use inspect for the total and poles for the mass split; compare with arithmetic-boundary-defect for a normalized residual.",
     "Inspection accepts odd prime bases through 251. The finite energy calculation is distinct from an asymptotic proof."},
    {"arithmetic-boundary-defect",
     "research",
     "Compare the exact finite collision energy with its cubic and secondary terms.",
     "Odd prime base or maximum base for a scan.",
     "Exact energy plus normalized numerical residuals involving logarithms.",
     "nfield arithmetic-boundary-defect scan 43",
     "Scan a range, then inspect a base whose residual merits a closer carry-table calculation.",
     "Odd prime bases through 251. Only logarithms/normalization are numerical; observed decay does not establish a new rate."},
    {"carry-completed-carrier",
     "research",
     "Construct a cyclic carrier with its carry seam or compare a coherent product-clock response.",
     "Compatible carrier parameters N,p,s; seam size; or product periods and endpoint steps.",
     "Exact coordinates, quotients, complement and seam energies; numerical product responses.",
     "nfield carry-completed-carrier seam 6",
     "Use seam independently, inspect for an eligible carrier, and product to resolve its Fourier response.",
     "Carrier inspect requires odd q=ord_p(s), p=2q+1 and q dividing N. Canonical graded assembly remains a separate question."},
    {"analytic",
     "compatibility",
     "Evaluate the legacy periodic-zeta example at a chosen base and lag.",
     "Digit base and positional lag.",
     "A primitive odd character factorization at character index 1 and s=1/2.",
     "nfield analytic 1 --base 5",
     "Use periodic-zeta-factorization inspect to choose the character and complex argument explicitly.",
     "Compatibility interface; read the printed normalization before comparing with newer families."},
    {"scale",
     "compatibility",
     "Obtain the predefined just major or chromatic interval table in its alignment coordinates.",
     "Major/chromatic selection, alpha/beta form and optional CSV.",
     "Musical interval ratios and their fixed alignment/deficit coordinates.",
     "nfield scale --chromatic --csv",
     "Export the table for tuning comparison; deficit-lattice ratio supports custom supported-field comparisons.",
     "The scale itself is predefined; this is not an arbitrary temperament optimizer."},
    {"coherence",
     "compatibility",
     "Explore the spectral geometry of a finite population of prime collision labels.",
     "Number of primes and digit base.",
     "Collision-label table and numerical coherence/eigenvalue diagnostics for the selected prime population.",
     "nfield coherence 30 --base 10",
     "Use finite-spectral-quotient for the explicit label-population quotient and heat-scale calculation.",
     "Compatibility output has its own normalizations; do not infer exact rational values from a printed decimal."},
    {"golden-threshold-table",
     "reference",
     "Read the predefined base-ten reciprocal-square threshold rows.",
     "No numerical inputs.",
     "The ten registered supported-resolution examples.",
     "nfield golden-threshold-table",
     "Use reciprocal-square-selection inspect to choose a different eligible prime, multiplier or base.",
     "Fixed reference table retained for compatibility."},
    {"spectrum",
     "compatibility",
     "Inspect cross-alignment matrix eigenvalues for a prime field.",
     "Prime modulus and digit base.",
     "Cross-alignment eigenvalues, multiplicities and the number of distinct levels.",
     "nfield spectrum 13 --base 10",
     "Use spectral-structure for orbit-frequency explanations and cross-alignment for the original matrix.",
     "This is the alignment-matrix spectrum, distinct from additive digit-bin power."},
    {"gate",
     "compatibility",
     "Inspect the legacy digit-collision gate at one prime.",
     "Prime modulus and digit base.",
     "Finite collision-gate values for the selected prime.",
     "nfield gate 13 --base 10",
     "Use collision-coordinate gate or bin-derangements family for the explicit mathematical-object interface.",
     "Finite prime/base gate; not a prime-distribution test."},
    {"derangements",
     "compatibility",
     "List zero-collision multipliers for a prime using the compatibility interface.",
     "Prime modulus and digit base.",
     "The finite deranging multiplier list.",
     "nfield derangements 13 --base 10",
     "Prefer bin-derangements family for the documented current operation.",
     "This legacy route is retained for older scripts."},
    {"silent_primes",
     "compatibility",
     "Inspect the legacy silence recipe for a base and lag.",
     "Digit base and lag.",
     "Finite silent-prime recipe and listed cases.",
     "nfield silent_primes 10 --lag 1",
     "Prefer silent-primes recipe or prime for focused current operations.",
     "Compatibility display; silence concerns the selected digit collision only."},
    {"gate_width",
     "verification",
     "Run the fixed legacy gate-width verification sweep.",
     "No adjustable sweep is supplied by this wrapper.",
     "PASS/FAIL results for the registered finite base/prime cases.",
     "nfield verify gate-width",
     "Use bin-derangements family <p> --base <b> to calculate a gate on your own inputs.",
     "The old --base wrapper label does not select the fixed verifier's test set."},
    {"fluctuation_sum",
     "compatibility",
     "Measure the legacy prime-weighted collision fluctuation over an explicit finite cutoff.",
     "Base, lag and prime cutoff.",
     "Finite cumulative fluctuation sums and reference comparisons.",
     "nfield fluctuation_sum --base 5 --lag 1 --primes 1000",
     "Vary the finite cutoff; use collision-characters for the corresponding channel decomposition.",
     "Always set --primes for a bounded run. A numerical trend does not prove an asymptotic."},
    {"character_components",
     "compatibility",
     "Inspect the legacy character decomposition of the base-squared collision table.",
     "Digit base.",
     "Finite table character magnitudes in the legacy CRT coordinates.",
     "nfield character_components --base 5",
     "Use collision-transform spectrum for the centered table, or collision-characters for prime-weighted residue streams.",
     "These base-squared table coordinates differ from the prime-cutoff character stream operation."},
    {"class_bias",
     "compatibility",
     "Compare finite prime-weighted collision bias across residue classes.",
     "Digit base and prime cutoff.",
     "Per-class finite bias values and sample counts.",
     "nfield class_bias --base 5 --primes 1000",
     "Compare several cutoffs at the same base before interpreting a class difference.",
     "Set a finite cutoff explicitly; class bias at one cutoff is not a limiting bias."},
    {"class_means",
     "compatibility",
     "Inspect the exact periodic-table means behind the legacy residue-class display.",
     "Digit base.",
     "Class means for the chosen finite collision table.",
     "nfield class_means --base 5",
     "Compare these table means with class_bias on a prime window.",
     "A table mean and a sampled prime mean use different populations."},
    {"centered_sum",
     "compatibility",
     "Measure a finite prime sum after removing the table's class means.",
     "Digit base and prime cutoff.",
     "Finite centered prime sums in the legacy display.",
     "nfield centered_sum --base 5 --primes 1000",
     "Use class_means to inspect the removed baseline; use collision-centering for lag-aware operations.",
     "The cutoff is finite and the weighted sum numerical."},
    {"neutrality",
     "compatibility",
     "Compare finite residue-three prime contributions with the legacy neutrality display.",
     "Digit base and prime cutoff.",
     "Channel totals and the finite neutrality comparison.",
     "nfield neutrality --base 5 --primes 1000",
     "Use residue-three-neutrality inspect/channels/split for explicit quotient carry and true residue channels.",
     "Set the cutoff explicitly. Internal table slices and actual prime residues must not be conflated."},
    {"neutrality_sweep",
     "reference",
     "Reproduce the fixed legacy neutrality sweep.",
     "No caller-selected numerical range.",
     "Registered finite neutrality rows.",
     "nfield neutrality_sweep",
     "Use residue-three-neutrality channels or split to choose the actual base and prime interval.",
     "Fixed compatibility reference; it is not a general-purpose sweep interface."},
    {"finite_det",
     "verification",
     "Run the fixed legacy finite-determination checks.",
     "No caller-selected test domain.",
     "Registered finite determination check results.",
     "nfield verify finite-det",
     "Use finite-determination inspect with an integer, base and lag for a usable calculation.",
     "Verification wrapper retained for older scripts."},
    {"mod3_means",
     "compatibility",
     "Inspect the legacy residue-three averages of a selected digit table.",
     "Digit base.",
     "The three table-slice means.",
     "nfield mod3_means 5",
     "Use residue-three-neutrality channels to distinguish these internal means from true lifted residue channels.",
     "These are finite table means, not an empirical prime-density calculation."},
    {"polarity_field",
     "compatibility",
     "Inspect the legacy signed collision pattern across the residue classes of a digit base.",
     "Digit base.",
     "The finite polarity table and its signed class structure.",
     "nfield polarity_field 5",
     "Compare with collision-table and collision-centering to identify the underlying values and centering convention.",
     "Polarity here is a table sign, not a Mobius sign or physical emission law."},
};

typedef struct { const char *name; const char *canonical; } GuideAlias;
static const GuideAlias aliases[] = {
    {"collision_table", "table"},
    {"mertens_growth", "fluctuation_sum"},
    {"centered-collision", "collision-centering"},
    {"collision-periodic-table", "collision-table"},
    {"neutrality-theorem", "residue-three-neutrality"},
    {"general-neutrality", "compatible-residue-channels"},
    {"goldbach-obstruction", "reflected-prime-pair-sign"},
    {"explore", "field"},
    {"reading-map", "commands"},
    {"verification-map", "verify"},
    {"legacy", "commands"},
};

const char *nfield_command_canonical_name(const char *name)
{
    if (name == NULL) return NULL;
    for (size_t i = 0; i < sizeof(aliases) / sizeof(aliases[0]); i++)
        if (strcmp(name, aliases[i].name) == 0) return aliases[i].canonical;
    for (size_t i = 0; i < sizeof(guides) / sizeof(guides[0]); i++)
        if (strcmp(name, guides[i].name) == 0) return guides[i].name;
    return NULL;
}

const NfieldCommandGuide *nfield_command_guide_lookup(const char *name)
{
    const char *canonical = nfield_command_canonical_name(name);
    if (canonical == NULL) return NULL;
    for (size_t i = 0; i < sizeof(guides) / sizeof(guides[0]); i++)
        if (strcmp(canonical, guides[i].name) == 0) return &guides[i];
    return NULL;
}

const char *nfield_command_purpose(const char *name)
{
    const NfieldCommandGuide *guide = nfield_command_guide_lookup(name);
    return guide ? guide->purpose : NULL;
}

static int named_action(const char *action, const char *names)
{
    if (!action) return 0;
    size_t length = strlen(action);
    for (const char *p = names; *p;) {
        while (*p == ' ') ++p;
        if (!*p) break;
        const char *end = strchr(p, ' ');
        size_t count = end ? (size_t)(end - p) : strlen(p);
        if (count == length && !strncmp(p, action, count)) return 1;
        p += count;
    }
    return 0;
}

int nfield_command_format_supported(const char *family, const char *action,
                                   const char *format)
{
    family = nfield_command_canonical_name(family);
    if (!family || !format) return 0;
    int json = !strcmp(format, "--json"), csv = !strcmp(format, "--csv");
    if (!json && !csv) return 0;
    if (!strcmp(family, "reset-forest") && action && !strcmp(action, "contracts"))
        return json;
    if (!strcmp(family, "reset-forest"))
        return !action || !strcmp(action, "(default)") ||
               named_action(action, "source project");
    if (json) {
        if (!strcmp(family, "commands")) return 1;
        if (!strcmp(family, "native-refinement"))
            return named_action(action, "detector transport probe-transport packet trace collision4 collision-families");
        return 0;
    }
    if (!strcmp(family, "survey") || !strcmp(family, "range") || !strcmp(family, "scale")) return 1;
    return 0;
}

int nfield_command_format_guard(int argc, char **argv)
{
    if (argc < 2) return 0;
    const char *format = NULL;
    int requested = 0, json = 0, csv = 0;
    for (int i = 2; i < argc; ++i) {
        if (!strcmp(argv[i], "--json") || !strcmp(argv[i], "--csv")) {
            ++requested;
            if (!strcmp(argv[i], "--json")) json = 1;
            else csv = 1;
            format = argv[i];
        } else if (!strncmp(argv[i], "--json=", 7) || !strncmp(argv[i], "--csv=", 6)) {
            fprintf(stderr, "Use %s without a value.\n", !strncmp(argv[i], "--json", 6) ? "--json" : "--csv");
            return 1;
        }
    }
    if (!format) return 0;
    const char *family = nfield_command_canonical_name(argv[1]);
    const char *action = argc > 2 ? argv[2] : NULL;
    if (family && !strcmp(family, "reset-forest") && action && action[0] >= '0' && action[0] <= '9') action = NULL;
    int supported = 1;
    if (json && !nfield_command_format_supported(argv[1], action, "--json")) {
        supported = 0; format = "--json";
    }
    if (csv && !nfield_command_format_supported(argv[1], action, "--csv")) {
        supported = 0; format = "--csv";
    }
    if (family && !strcmp(family, "verify"))
        supported = argc >= 4 && !strcmp(argv[2], "reset-forest") &&
                    !strcmp(argv[3], "contracts") && json && !csv;
    if (supported) {
        /* These parsers reject duplicate formats with their own established
         * diagnostics and exit codes, before doing any calculation. */
        int native_validation = family && (!strcmp(family, "reset-forest") ||
            !strcmp(family, "verify") || !strcmp(family, "native-refinement"));
        if (requested > 1 && !native_validation) {
            fputs("Choose one output format: --json or --csv.\n", stderr);
            return 1;
        }
        return 0;
    }
    fprintf(stderr, "%s is not supported for nfield %s%s%s.\n",
            format, argv[1], action && action[0] != '-' ? " " : "",
            action && action[0] != '-' ? action : "");
    fprintf(stderr, "Use nfield help %s for supported output and options.\n", argv[1]);
    return 1;
}

static void paragraph(const char *label, const char *text)
{
    const size_t width = 76;
    size_t column = 2;
    printf("%s\n  ", label);
    while (*text) {
        const char *end = text;
        while (*end && *end != ' ') end++;
        size_t length = (size_t)(end - text);
        if (column > 2 && column + length + 1 > width) {
            printf("\n  ");
            column = 2;
        } else if (column > 2) {
            putchar(' ');
            column++;
        }
        (void)fwrite(text, 1, length, stdout);
        column += length;
        text = *end ? end + 1 : end;
    }
    printf("\n\n");
}

int nfield_command_guide(const char *name)
{
    const NfieldCommandGuide *guide = nfield_command_guide_lookup(name);
    if (guide == NULL) return 0;
    printf("nfield %s\n\n", name);
    if (strcmp(name, guide->name) != 0)
        printf("  Related interface: nfield %s\n\n", guide->name);
    paragraph(strcmp(guide->kind, "verification") == 0 ? "Check purpose" : "Use this for", guide->purpose);
    paragraph("Your inputs", guide->inputs);
    paragraph("Result", guide->outputs);
    printf("Start here\n  %s\n\n", guide->example);
    paragraph("Workflow", guide->workflow);
    paragraph("Scope", guide->limits);
    return 1;
}

const NfieldActionGuide *nfield_action_guide_lookup(const char *family, const char *action)
{
    family = nfield_command_canonical_name(family);
    if (!family || !action) return NULL;
    for (size_t i = 0; i < sizeof(action_guides) / sizeof(action_guides[0]); ++i)
        if (!strcmp(family, action_guides[i].family) &&
            !strcmp(action, action_guides[i].name)) return &action_guides[i];
    return NULL;
}

const NfieldActionGuide *nfield_action_guide_at(const char *family, size_t index)
{
    family = nfield_command_canonical_name(family);
    if (!family) return NULL;
    for (size_t i = 0; i < sizeof(action_guides) / sizeof(action_guides[0]); ++i)
        if (!strcmp(family, action_guides[i].family) && index-- == 0)
            return &action_guides[i];
    return NULL;
}

static int print_action_guide(const NfieldActionGuide *guide)
{
    if (!guide) return 0;
    printf("Action: %s\n\n", guide->name);
    paragraph(!strcmp(guide->kind, "verification") ? "Check purpose" : "Use this action for",
              guide->purpose);
    printf("Usage\n  %s\n\n", guide->syntax);
    paragraph("Action inputs", guide->inputs);
    paragraph("Action result", guide->outputs);
    printf("Action example\n  %s\n\n", guide->example);
    paragraph("Action scope", guide->limits);
    return 1;
}

int nfield_action_guide(const char *family, const char *action)
{
    return print_action_guide(nfield_action_guide_lookup(family, action));
}

const NfieldActionGuide *nfield_verify_action_guide_lookup(const char *family, const char *action)
{
    const char *legacy = nfield_verify_action_legacy_name(family, action);
    return legacy ? nfield_action_guide_lookup(family, legacy) : NULL;
}

int nfield_verify_action_guide(const char *family, const char *action)
{
    return print_action_guide(nfield_verify_action_guide_lookup(family, action));
}
