/* Direct API driver and output-preservation checks for the independent oracle. */
#include "../src/weighted_remainder_joint.h"
#include <stdio.h>
#include <string.h>

static int edge_checks(void)
{
    mpq_t q;
    mpz_t r, l;
    mpq_init(q);
    mpz_inits(r, l, NULL);
    unsigned k[9] = {2,3,4,5,6,7,8,9,10};
    unsigned h[9] = {0};
    unsigned p[9] = {0};
    unsigned checks = 0;
#define PREPARE() do { mpq_set_ui(q,17,19); mpz_set_ui(r,23); mpz_set_ui(l,29); } while(0)
#define FAILS(call) do { PREPARE(); ++checks; if ((call) || mpq_cmp_ui(q,17,19) || \
    mpz_cmp_ui(r,23) || mpz_cmp_ui(l,29)) { fprintf(stderr,"edge failure %u\n",checks); return 1; } } while(0)
    FAILS(weighted_remainder_joint_crt_q(q,r,l,9,k,h));
    FAILS(weighted_remainder_joint_crt_q(q,r,l,1,NULL,h));
    FAILS(weighted_remainder_joint_crt_q(q,r,l,1,k,NULL));
    FAILS(weighted_remainder_joint_crt_q(q,r,r,1,k,h));
    FAILS(weighted_remainder_joint_crt_q(q,mpq_numref(q),l,1,k,h));
    FAILS(weighted_remainder_joint_crt_q(q,mpq_denref(q),l,1,k,h));
    FAILS(weighted_remainder_joint_crt_q(q,r,mpq_numref(q),1,k,h));
    FAILS(weighted_remainder_joint_crt_q(q,r,mpq_denref(q),1,k,h));
    k[0]=0; FAILS(weighted_remainder_joint_crt_q(q,r,l,1,k,h));
    k[0]=1; FAILS(weighted_remainder_joint_crt_q(q,r,l,1,k,h));
    k[0]=241; FAILS(weighted_remainder_joint_crt_q(q,r,l,1,k,h));
    k[0]=2; h[0]=241; FAILS(weighted_remainder_joint_crt_q(q,r,l,1,k,h)); h[0]=0;
    FAILS(weighted_remainder_forcing_q(q,0));
    FAILS(weighted_remainder_forcing_q(q,241));
    FAILS(weighted_remainder_empirical_moment_q(q,0,0,1,h,p));
    FAILS(weighted_remainder_empirical_moment_q(q,241,0,1,h,p));
    FAILS(weighted_remainder_empirical_moment_q(q,1,2,1,h,p));
    FAILS(weighted_remainder_empirical_moment_q(q,1,0,9,h,p));
    FAILS(weighted_remainder_empirical_moment_q(q,1,0,1,NULL,p));
    FAILS(weighted_remainder_empirical_moment_q(q,1,0,1,h,NULL));
    h[0]=240; FAILS(weighted_remainder_empirical_moment_q(q,1,0,1,h,p)); h[0]=0;
    p[0]=17; FAILS(weighted_remainder_empirical_moment_q(q,1,0,1,h,p));
    p[0]=16; p[1]=1; FAILS(weighted_remainder_empirical_moment_q(q,1,0,2,h,p)); p[0]=p[1]=0;
    FAILS(weighted_remainder_cutoff_joint_moment_q(q,1,1,h));
    FAILS(weighted_remainder_cutoff_joint_moment_q(q,241,1,h));
    FAILS(weighted_remainder_cutoff_joint_moment_q(q,2,9,h));
    FAILS(weighted_remainder_cutoff_joint_moment_q(q,2,1,NULL));
    FAILS(weighted_remainder_cutoff_joint_moment_q(q,6,7,h));
    h[0]=241; FAILS(weighted_remainder_cutoff_joint_moment_q(q,2,1,h)); h[0]=0;
    FAILS(weighted_remainder_block_q(q,241,0));
    FAILS(weighted_remainder_block_q(q,0,241));
    FAILS(weighted_remainder_block_q(q,240,1));
    ++checks;
    if (!weighted_remainder_joint_crt_q(q,r,l,0,NULL,NULL) || mpq_cmp_ui(q,1,1) ||
        mpz_cmp_ui(r,0) || mpz_cmp_ui(l,1)) return 1;
    ++checks;
    if (!weighted_remainder_empirical_moment_q(q,240,1,0,NULL,NULL) || mpq_cmp_ui(q,1,1)) return 1;
    ++checks;
    if (!weighted_remainder_cutoff_joint_moment_q(q,240,0,NULL) || mpq_cmp_ui(q,1,1)) return 1;
    ++checks;
    if (!weighted_remainder_block_q(q,240,0) || mpq_sgn(q)) return 1;
    printf("API_EDGE_CHECKS=%u\n",checks);
    mpq_clear(q);
    mpz_clears(r,l,NULL);
    return 0;
}

int main(int argc, char **argv)
{
    if (argc==2 && strcmp(argv[1],"--edges")==0) return edge_checks();
    mpq_t q;
    mpz_t r,l;
    mpq_init(q);
    mpz_inits(r,l,NULL);
    char mode;
    unsigned dimension=0, first=0, kind=0, left[8], right[8];
    while (scanf(" %c",&mode)==1) {
        int ok=0;
        if (mode=='C') {
            if (scanf("%u",&dimension)!=1 || dimension>8) return 2;
            for (unsigned i=0;i<dimension;++i) if (scanf("%u%u",&left[i],&right[i])!=2) return 2;
            ok=weighted_remainder_joint_crt_q(q,r,l,dimension,left,right);
            if (ok) gmp_printf("C %Qd %Zd %Zd\n",q,r,l);
        } else if (mode=='M') {
            if (scanf("%u%u%u",&first,&kind,&dimension)!=3 || dimension>8) return 2;
            for (unsigned i=0;i<dimension;++i) if (scanf("%u%u",&left[i],&right[i])!=2) return 2;
            ok=weighted_remainder_empirical_moment_q(q,first,kind,dimension,left,right);
            if (ok) gmp_printf("M %Qd\n",q);
        } else if (mode=='H') {
            if (scanf("%u%u",&first,&dimension)!=2 || dimension>8) return 2;
            for (unsigned i=0;i<dimension;++i) if (scanf("%u",&left[i])!=1) return 2;
            ok=weighted_remainder_cutoff_joint_moment_q(q,first,dimension,left);
            if (ok) gmp_printf("H %Qd\n",q);
        } else if (mode=='F') {
            if (scanf("%u",&first)!=1) return 2;
            ok=weighted_remainder_forcing_q(q,first);
            if (ok) gmp_printf("F %Qd\n",q);
        } else if (mode=='B') {
            if (scanf("%u%u",&first,&dimension)!=2) return 2;
            ok=weighted_remainder_block_q(q,first,dimension);
            if (ok) gmp_printf("B %Qd\n",q);
        }
        if (!ok) puts("INVALID");
    }
    mpq_clear(q);
    mpz_clears(r,l,NULL);
    return 0;
}
