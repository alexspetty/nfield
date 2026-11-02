#ifndef NFIELD_WEIGHTED_REMAINDER_JOINT_H
#define NFIELD_WEIGHTED_REMAINDER_JOINT_H

#include "weighted_remainder_pairing.h"

/* Finite resource bounds, not restrictions on the mathematical theorems. */
#define WEIGHTED_REMAINDER_JOINT_MAX 8
#define WEIGHTED_REMAINDER_MOMENT_DEGREE_MAX 16
#define WEIGHTED_REMAINDER_JOINT_TUPLE_MAX 65536

/* Exact probability of k_i | n+h_i under uniform residues/Haar.
 * 0<=dimension<=8; 2<=periods[i]<=240; 0<=shifts[i]<=240.
 * Empty lists have probability 1, residue 0 and period 1. An incompatible
 * list is a successful result with probability/residue 0 and the full lcm.
 * Otherwise residue is the unique representative in [0,period).
 * All three outputs must be initialized with disjoint storage, including
 * the numerator and denominator of probability. Failure preserves all.
 * Arrays may be NULL only when dimension is zero. */
int weighted_remainder_joint_crt_q(mpq_t probability, mpz_t residue, mpz_t period,
                                    unsigned dimension, const unsigned *periods,
                                    const unsigned *shifts);

/* Full positive-integer f, with 1<=n<=240; g is the existing reset_q API. */
int weighted_remainder_forcing_q(mpq_t out, unsigned n);

/* Average of product_i f(n+h_i)^p_i or g(n+h_i)^p_i on n=1..length.
 * kind=0 selects f, kind=1 selects g. 1<=length<=240, dimension<=8,
 * each shift<=240-length, and sum of powers<=16. Empty products equal 1.
 * This is an exact finite average, without a claimed infinite-limit error. */
int weighted_remainder_empirical_moment_q(mpq_t out, unsigned length, unsigned kind,
                                         unsigned dimension, const unsigned *shifts,
                                         const unsigned *powers);

/* Exact Haar product moment for f_M=sum_{2<=k<=M} k*w_k*1_(k|x).
 * 2<=cutoff<=240, dimension<=8, shifts<=240, (cutoff-1)^dimension<=65536.
 * The output is a finite positive partial sum of the full CRT series;
 * no uncomputed infinite tail is silently included. Empty products equal 1. */
int weighted_remainder_cutoff_joint_moment_q(mpq_t out, unsigned cutoff,
                                            unsigned dimension, const unsigned *shifts);

/* Exact D_(start+length)-D_start by full integer resets. start>=0,
 * length>=0 and start+length<=240; length zero returns zero.
 * Single-output APIs require initialized out and preserve it on failure. */
int weighted_remainder_block_q(mpq_t out, unsigned start, unsigned length);

int weighted_remainder_joint_command(int argc, char **argv);

#endif
