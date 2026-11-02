#include "weighted_remainder_harmonic_root.h"
#include <stdio.h>
#include <stdlib.h>

#define RFIELDS(X) X(harmonic_tail_upper) X(cubic_prefix_lower) X(cubic_prefix_upper) X(cubic_tail_upper) \
    X(cubic_lower) X(cubic_upper) X(sine_prefix_lower) X(sine_prefix_upper) X(sine_tail_upper) X(sine_lower) \
    X(sine_upper) X(zeta_lower) X(zeta_upper) X(angle_weight_lower) X(angle_weight_upper) X(identity_lower) X(identity_upper)
static unsigned edges;
static void check(int ok) { ++edges;if (!ok) { fprintf(stderr,"harmonic root edge %u failed\n",edges);exit(1); } }
static void rect_print(const WeightedRemainderComplex *s)
{
    gmp_printf(" %Qd %Qd %Qd %Qd",s->real_lower,s->real_upper,s->imag_lower,s->imag_upper);
}
static void rect_set(WeightedRemainderComplex *s)
{
    mpq_set_si(s->real_lower,-31,7);mpq_set_si(s->real_upper,11,13);
    mpq_set_si(s->imag_lower,-17,19);mpq_set_si(s->imag_upper,23,29);
}
static int rect_same(const WeightedRemainderComplex *s)
{
    return !mpq_cmp_si(s->real_lower,-31,7) && !mpq_cmp_si(s->real_upper,11,13) &&
        !mpq_cmp_si(s->imag_lower,-17,19) && !mpq_cmp_si(s->imag_upper,23,29);
}
static void polylog_edges(void)
{
    WeightedRemainderHarmonicPolylog s,t;weighted_remainder_harmonic_polylog_init(&s);
    weighted_remainder_harmonic_polylog_init(&t);s.cutoff=71;s.binary_exponent=72;
    mpq_set_si(s.z_real,-13,11);mpq_set_si(s.z_imag,-13,11);mpq_set_si(s.tail_upper,-13,11);
    rect_set(&s.prefix);rect_set(&s.value);
    mpq_t re,im;mpq_inits(re,im,NULL);
    for (unsigned i=0;i<8;++i) {
        mpq_set_ui(re,1,2);mpq_set_ui(im,0,1);unsigned N=3;
        if (i==0) N=0;
        if (i==1) N=241;
        if (i==2) { mpq_set_ui(re,3,4);mpq_set_ui(im,3,4); }
        if (i==3) mpz_set_ui(mpq_denref(re),0);
        if (i==4) mpz_set_si(mpq_denref(re),-2);
        if (i==5) { mpz_set_ui(mpq_numref(re),2);mpz_set_ui(mpq_denref(re),4); }
        if (i==6) { mpz_set_ui(mpq_numref(re),1);mpz_ui_pow_ui(mpq_denref(re),2,63); }
        if (i==7) { mpz_ui_pow_ui(mpq_numref(re),2,63);mpz_set_ui(mpq_denref(re),1); }
        check(!weighted_remainder_harmonic_polylog_compute(&s,re,im,N));
        check(s.cutoff==71 && s.binary_exponent==72 && !mpq_cmp_si(s.z_real,-13,11) &&
            !mpq_cmp_si(s.z_imag,-13,11) && !mpq_cmp_si(s.tail_upper,-13,11));
        check(rect_same(&s.prefix) && rect_same(&s.value));
    }
    mpq_set_ui(re,3,5);mpq_set_ui(im,4,5);
    check(!weighted_remainder_harmonic_polylog_compute(NULL,re,im,3));
    check(!weighted_remainder_harmonic_polylog_compute(&s,NULL,im,3));
    check(!weighted_remainder_harmonic_polylog_compute(&s,re,NULL,3));
    check(weighted_remainder_harmonic_polylog_compute(&t,re,im,13));
    mpq_ptr fields[]={s.z_real,s.z_imag,s.tail_upper,s.prefix.real_lower,s.prefix.real_upper,
        s.prefix.imag_lower,s.prefix.imag_upper,s.value.real_lower,s.value.real_upper,s.value.imag_lower,s.value.imag_upper};
    for (unsigned i=0;i<11;++i) for (unsigned coordinate=0;coordinate<2;++coordinate) {
        mpq_set(fields[i],coordinate?im:re);
        check(weighted_remainder_harmonic_polylog_compute(&s,coordinate?re:fields[i],coordinate?fields[i]:im,13));
        check(!mpq_cmp(s.z_real,t.z_real) && !mpq_cmp(s.z_imag,t.z_imag) &&
            !mpq_cmp(s.prefix.real_lower,t.prefix.real_lower) && !mpq_cmp(s.prefix.imag_lower,t.prefix.imag_lower) &&
            !mpq_cmp(s.value.real_lower,t.value.real_lower) && !mpq_cmp(s.value.real_upper,t.value.real_upper) &&
            !mpq_cmp(s.value.imag_lower,t.value.imag_lower) && !mpq_cmp(s.value.imag_upper,t.value.imag_upper));
    }
    mpq_set_ui(re,0,1);mpq_set_ui(im,0,1);
    check(weighted_remainder_harmonic_polylog_compute(&s,re,im,240));
    check(!mpq_sgn(s.tail_upper) && !mpq_sgn(s.value.real_lower) && !mpq_sgn(s.value.real_upper) &&
        !mpq_sgn(s.value.imag_lower) && !mpq_sgn(s.value.imag_upper));
    mpq_set_ui(re,1,3);check(weighted_remainder_harmonic_polylog_compute(&s,re,re,3));
    mpq_clears(re,im,NULL);weighted_remainder_harmonic_polylog_clear(&s);weighted_remainder_harmonic_polylog_clear(&t);
}
static void edge_checks(void)
{
    polylog_edges();WeightedRemainderHarmonicRoot s;weighted_remainder_harmonic_root_init(&s);
    s.denominator=71;s.numerator=72;s.cutoff=73;s.zeta_cutoff=74;s.binary_exponent=75;
    rect_set(&s.phase);rect_set(&s.harmonic_prefix);rect_set(&s.harmonic);
#define SET(f) mpq_set_si(s.f,-13,11);
    RFIELDS(SET)
#undef SET
    unsigned bad[][4]={{0,0,1,1},{241,0,1,1},{3,3,1,1},{3,1,0,1},{3,1,241,1},{3,1,1,0},{3,1,1,241}};
    for (unsigned i=0;i<sizeof(bad)/sizeof(*bad);++i) {
        check(!weighted_remainder_harmonic_root_compute(&s,bad[i][0],bad[i][1],bad[i][2],bad[i][3]));
        check(s.denominator==71 && s.numerator==72 && s.cutoff==73 && s.zeta_cutoff==74 && s.binary_exponent==75);
        check(rect_same(&s.phase) && rect_same(&s.harmonic_prefix) && rect_same(&s.harmonic));
#define SAME(f) check(!mpq_cmp_si(s.f,-13,11));
        RFIELDS(SAME)
#undef SAME
    }
    check(!weighted_remainder_harmonic_root_compute(NULL,3,1,1,1));
    check(weighted_remainder_harmonic_root_compute(&s,1,0,240,1));
    check(!mpq_sgn(s.harmonic.imag_lower) && !mpq_sgn(s.harmonic.imag_upper) && !mpq_sgn(s.sine_lower) && !mpq_sgn(s.sine_upper));
    check(weighted_remainder_harmonic_root_compute(&s,240,239,1,240));
    weighted_remainder_harmonic_root_clear(&s);
    WeightedRemainderHarmonicRootAverage a;weighted_remainder_harmonic_root_average_init(&a);
    a.modulus=71;a.cutoff=72;a.binary_exponent=73;rect_set(&a.root_average_prefix);
    mpq_set_si(a.selected_prefix,-13,11);mpq_set_si(a.tail_upper,-13,11);
    mpq_set_si(a.lower,-13,11);mpq_set_si(a.upper,-13,11);
    unsigned invalid[][2]={{0,1},{241,1},{3,0},{3,241}};
    for (unsigned i=0;i<4;++i) {
        check(!weighted_remainder_harmonic_root_average_compute(&a,invalid[i][0],invalid[i][1]));
        check(a.modulus==71 && a.cutoff==72 && a.binary_exponent==73 && rect_same(&a.root_average_prefix));
        check(!mpq_cmp_si(a.selected_prefix,-13,11) && !mpq_cmp_si(a.tail_upper,-13,11) &&
            !mpq_cmp_si(a.lower,-13,11) && !mpq_cmp_si(a.upper,-13,11));
    }
    check(!weighted_remainder_harmonic_root_average_compute(NULL,3,1));
    check(weighted_remainder_harmonic_root_average_compute(&a,240,1));
    check(!mpq_sgn(a.selected_prefix));weighted_remainder_harmonic_root_average_clear(&a);
    mpq_t l,u,r,v;mpq_inits(l,u,r,v,NULL);mpz_t n;mpz_init_set_si(n,-17);mpq_ptr fields[]={l,u,r,v};
    for (unsigned i=0;i<4;++i) mpq_set_si(fields[i],-13,11);
    for (unsigned i=0;i<4;++i) for (unsigned j=i+1;j<4;++j) {
        mpq_ptr p[]={l,u,r,v};p[j]=p[i];
        check(!weighted_remainder_sine_transform_q(p[0],p[1],p[2],p[3],3,n));
        for (unsigned k=0;k<4;++k) check(!mpq_cmp_si(fields[k],-13,11));
    }
    for (unsigned i=0;i<4;++i) {
        mpq_ptr p[]={l,u,r,v};p[i]=NULL;
        check(!weighted_remainder_sine_transform_q(p[0],p[1],p[2],p[3],3,n));
    }
    check(!weighted_remainder_sine_transform_q(l,u,r,v,3,NULL));
    check(!weighted_remainder_sine_transform_q(l,u,r,v,0,n));
    check(!weighted_remainder_sine_transform_q(l,u,r,v,241,n));
    check(weighted_remainder_sine_transform_q(l,u,r,v,1,n));
    for (unsigned k=0;k<4;++k) check(!mpq_sgn(fields[k]));
    mpz_set_ui(n,240);check(weighted_remainder_sine_transform_q(l,u,r,v,240,n));
    for (unsigned k=0;k<4;++k) check(!mpq_sgn(fields[k]));
    mpz_clear(n);mpq_clears(l,u,r,v,NULL);
}
int main(void)
{
    edge_checks();printf("EDGES %u\n",edges);char mode;
    while (scanf(" %c",&mode)==1) {
        unsigned q,a,N,K;
        if (mode=='H') {
            char re[512],im[512];if (scanf(" %u %511s %511s",&N,re,im)!=3) return 2;
            mpq_t r,i;mpq_inits(r,i,NULL);int parsed=!mpq_set_str(r,re,10) && !mpq_set_str(i,im,10);
            if (parsed && mpz_sgn(mpq_denref(r)) && mpz_sgn(mpq_denref(i))) { mpq_canonicalize(r);mpq_canonicalize(i); }
            else parsed=0;
            WeightedRemainderHarmonicPolylog s;weighted_remainder_harmonic_polylog_init(&s);
            int ok=parsed && weighted_remainder_harmonic_polylog_compute(&s,r,i,N);printf("H %d",ok);
            if (ok) {
                printf(" %u %u",s.cutoff,s.binary_exponent);gmp_printf(" %Qd %Qd %Qd",s.z_real,s.z_imag,s.tail_upper);
                rect_print(&s.prefix);rect_print(&s.value);
            }
            putchar('\n');weighted_remainder_harmonic_polylog_clear(&s);mpq_clears(r,i,NULL);
        } else if (mode=='R') {
            if (scanf(" %u %u %u %u",&q,&a,&N,&K)!=4) return 2;
            WeightedRemainderHarmonicRoot s;weighted_remainder_harmonic_root_init(&s);
            int ok=weighted_remainder_harmonic_root_compute(&s,q,a,N,K);printf("R %d",ok);
            if (ok) {
                printf(" %u %u %u %u %u",s.denominator,s.numerator,s.cutoff,s.zeta_cutoff,s.binary_exponent);
                rect_print(&s.phase);rect_print(&s.harmonic_prefix);rect_print(&s.harmonic);
#define PRINT(f) gmp_printf(" %Qd",s.f);
                RFIELDS(PRINT)
#undef PRINT
            }
            putchar('\n');weighted_remainder_harmonic_root_clear(&s);
        } else if (mode=='A') {
            if (scanf(" %u %u",&q,&N)!=2) return 2;
            WeightedRemainderHarmonicRootAverage s;weighted_remainder_harmonic_root_average_init(&s);
            int ok=weighted_remainder_harmonic_root_average_compute(&s,q,N);printf("A %d",ok);
            if (ok) {
                printf(" %u %u %u",s.modulus,s.cutoff,s.binary_exponent);rect_print(&s.root_average_prefix);
                gmp_printf(" %Qd %Qd %Qd %Qd",s.selected_prefix,s.tail_upper,s.lower,s.upper);
            }
            putchar('\n');weighted_remainder_harmonic_root_average_clear(&s);
        } else if (mode=='S') {
            char freq[1024];if (scanf(" %u %1023s",&q,freq)!=2) return 2;
            mpz_t n;mpz_init(n);int parsed=!mpz_set_str(n,freq,10);
            mpq_t l,u,r,v;mpq_inits(l,u,r,v,NULL);
            int ok=parsed && weighted_remainder_sine_transform_q(l,u,r,v,q,n);printf("S %d",ok);
            if (ok) gmp_printf(" %Qd %Qd %Qd %Qd",l,u,r,v);
            putchar('\n');mpz_clear(n);mpq_clears(l,u,r,v,NULL);
        } else return 3;
    }
    return ferror(stdin)?4:0;
}
