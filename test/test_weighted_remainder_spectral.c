#include "../src/weighted_remainder_spectral.h"
#include <stdio.h>
#include <stdlib.h>

static unsigned edges;
#define CHECK(x) do { ++edges;if (!(x)) { fprintf(stderr,"edge failed line %d: %s\n",__LINE__,#x);exit(1); } } while (0)

static void fields(WeightedRemainderSpectralMean *s,mpq_ptr *v)
{
    mpq_ptr a[]={s->x,s->h_sum,s->h_mean,s->correction_floor_sum,s->correction_floor_mean,
        s->correction_series_prefix,s->product_lower,s->product_upper,
        s->nu_sum_lower,s->nu_sum_upper,s->nu_square_sum_lower,s->nu_square_sum_upper,
        s->nu_mean_lower,s->nu_mean_upper,s->nu_square_mean_lower,s->nu_square_mean_upper,
        s->first_prefix_lower,s->first_prefix_upper,s->first_tail_upper,s->first_lower,s->first_upper,
        s->second_prefix_lower,s->second_prefix_upper,s->second_tail_upper,s->second_lower,s->second_upper,
        s->nu_first_mean_bound,s->nu_second_mean_bound};
    for (unsigned i=0;i<28;++i) v[i]=a[i];
}

static void tail_fields(WeightedRemainderSpectralTail *s,mpq_ptr *v)
{
    mpq_ptr a[]={s->product_lower,s->product_upper,s->amplitude_leading_lower,s->amplitude_leading_upper,
        s->log_q_lower,s->log_q_upper,s->log_b_lower,s->log_b_upper,
        s->weighted_band_lower,s->weighted_band_upper,s->weighted_remainder_upper,
        s->weighted_tail_lower,s->weighted_tail_upper,s->energy_band_lower,s->energy_band_upper,
        s->energy_remainder_upper,s->projection_tail_lower,s->projection_tail_upper,
        s->weighted_leading_lower,s->weighted_leading_upper,s->energy_leading_lower,s->energy_leading_upper};
    for (unsigned i=0;i<22;++i) v[i]=a[i];
}

static int tail_sentinel(WeightedRemainderSpectralTail *s)
{
    if (s->cutoff!=11 || s->band_cutoff!=13 || s->period_cutoff!=17 || s->prime_cutoff!=19 ||
        s->constant_cutoff!=23 || s->period_binary_exponent!=29) return 0;
    mpq_ptr v[22];tail_fields(s,v);
    for (unsigned i=0;i<22;++i) if (mpq_cmp_ui(v[i],i+1,i+2)) return 0;
    return 1;
}

static void tail_edges(void)
{
    mpq_t a,b,c,d;mpq_inits(a,b,c,d,NULL);mpq_ptr v[]={a,b,c,d};
    for (unsigned i=0;i<4;++i) mpq_set_ui(v[i],i+1,i+2);
    unsigned invalid[][2]={{0,2},{1,2},{241,2},{~0U,2},{2,0},{2,1},{2,241},{2,~0U}};
    for (unsigned i=0;i<8;++i) CHECK(!weighted_remainder_spectral_energy_q(a,b,c,d,invalid[i][0],invalid[i][1]));
    for (unsigned i=0;i<4;++i) {
        mpq_ptr args[]={a,b,c,d};args[i]=NULL;
        CHECK(!weighted_remainder_spectral_energy_q(args[0],args[1],args[2],args[3],2,2));
        for (unsigned j=i+1;j<4;++j) {
            mpq_ptr pair[]={a,b,c,d};pair[j]=pair[i];
            CHECK(!weighted_remainder_spectral_energy_q(pair[0],pair[1],pair[2],pair[3],2,2));
        }
    }
    for (unsigned i=0;i<4;++i) CHECK(!mpq_cmp_ui(v[i],i+1,i+2));
    WeightedRemainderSpectralTail s;weighted_remainder_spectral_tail_init(&s);mpq_ptr f[22];tail_fields(&s,f);
    s.cutoff=11;s.band_cutoff=13;s.period_cutoff=17;s.prime_cutoff=19;s.constant_cutoff=23;s.period_binary_exponent=29;
    for (unsigned i=0;i<22;++i) mpq_set_ui(f[i],i+1,i+2);
    CHECK(!weighted_remainder_spectral_tail_compute(NULL,1,4,2,1,1));
    unsigned bad[][5]={{0,4,2,1,1},{5,4,2,1,1},{1,3,2,1,1},{1,241,2,1,1},
        {1,4,1,1,1},{1,4,241,1,1},{1,4,2,0,1},{1,4,2,241,1},{1,4,2,1,0},{1,4,2,1,241}};
    for (unsigned i=0;i<10;++i) {
        CHECK(!weighted_remainder_spectral_tail_compute(&s,bad[i][0],bad[i][1],bad[i][2],bad[i][3],bad[i][4]));
        CHECK(tail_sentinel(&s));
    }
    for (unsigned j=0;j<5;++j) {
        unsigned args[]={1,4,2,1,1};args[j]=~0U;
        CHECK(!weighted_remainder_spectral_tail_compute(&s,args[0],args[1],args[2],args[3],args[4]));CHECK(tail_sentinel(&s));
    }
    CHECK(weighted_remainder_spectral_tail_compute(&s,240,240,240,240,240));
    CHECK(!mpq_sgn(s.weighted_band_lower) && !mpq_sgn(s.energy_band_upper));
    CHECK(weighted_remainder_spectral_tail_compute(&s,1,4,2,1,1));
    CHECK(!mpq_sgn(s.weighted_leading_upper) && !mpq_sgn(s.energy_leading_upper));
    weighted_remainder_spectral_tail_clear(&s);mpq_clears(a,b,c,d,NULL);
}

static int sentinel(WeightedRemainderSpectralMean *s)
{
    if (s->floor_x!=17 || s->prime_cutoff!=19 || s->prime_tail_binary_exponent!=23) return 0;
    mpq_ptr v[28];fields(s,v);
    for (unsigned i=0;i<28;++i) if (mpq_cmp_ui(v[i],i+1,i+2)) return 0;
    return 1;
}

static void edge_checks(void)
{
    mpq_t a,b,x;mpq_inits(a,b,x,NULL);mpq_set_ui(a,5,7);mpq_set_ui(b,11,13);
    CHECK(!weighted_remainder_spectral_factors_q(a,b,0));
    CHECK(!weighted_remainder_spectral_factors_q(a,b,4));
    CHECK(!weighted_remainder_spectral_factors_q(a,b,241));
    CHECK(!weighted_remainder_spectral_factors_q(a,b,~0U));
    CHECK(!weighted_remainder_spectral_factors_q(a,a,2));
    CHECK(!weighted_remainder_spectral_factors_q(NULL,b,2));
    CHECK(!weighted_remainder_spectral_factors_q(a,NULL,2));
    CHECK(!weighted_remainder_spectral_arithmetic_q(a,b,241));
    CHECK(!weighted_remainder_spectral_arithmetic_q(a,b,~0U));
    CHECK(!weighted_remainder_spectral_arithmetic_q(a,a,1));
    CHECK(!weighted_remainder_spectral_arithmetic_q(NULL,b,1));
    CHECK(!weighted_remainder_spectral_arithmetic_q(a,NULL,1));
    CHECK(!weighted_remainder_spectral_product_q(a,b,0));
    CHECK(!weighted_remainder_spectral_product_q(a,b,241));
    CHECK(!weighted_remainder_spectral_product_q(a,b,~0U));
    CHECK(!weighted_remainder_spectral_product_q(a,a,1));
    CHECK(!weighted_remainder_spectral_product_q(NULL,b,1));
    CHECK(!weighted_remainder_spectral_product_q(a,NULL,1));
    CHECK(!mpq_cmp_ui(a,5,7) && !mpq_cmp_ui(b,11,13));
    WeightedRemainderSpectralMean s;weighted_remainder_spectral_mean_init(&s);
    mpq_ptr v[28];fields(&s,v);s.floor_x=17;s.prime_cutoff=19;s.prime_tail_binary_exponent=23;
    for (unsigned i=0;i<28;++i) mpq_set_ui(v[i],i+1,i+2);
    CHECK(!weighted_remainder_spectral_mean_compute(NULL,a,1));
    CHECK(!weighted_remainder_spectral_mean_compute(&s,NULL,1));CHECK(sentinel(&s));
    mpq_set_ui(x,2,1);
    CHECK(!weighted_remainder_spectral_mean_compute(&s,x,0));CHECK(sentinel(&s));
    CHECK(!weighted_remainder_spectral_mean_compute(&s,x,241));CHECK(sentinel(&s));
    CHECK(!weighted_remainder_spectral_mean_compute(&s,x,~0U));CHECK(sentinel(&s));
    const char *invalid[]={"0","-1","1/2","240001/1000"};
    for (unsigned i=0;i<4;++i) {
        CHECK(!mpq_set_str(x,invalid[i],10));mpq_canonicalize(x);
        CHECK(!weighted_remainder_spectral_mean_compute(&s,x,1));CHECK(sentinel(&s));
    }
    mpz_set_ui(mpq_numref(x),2);mpz_set_ui(mpq_denref(x),2);
    CHECK(!weighted_remainder_spectral_mean_compute(&s,x,1));CHECK(sentinel(&s));
    mpz_set_ui(mpq_numref(x),1);mpz_set_ui(mpq_denref(x),0);
    CHECK(!weighted_remainder_spectral_mean_compute(&s,x,1));CHECK(sentinel(&s));
    mpz_set_si(mpq_numref(x),-1);mpz_set_si(mpq_denref(x),-1);
    CHECK(!weighted_remainder_spectral_mean_compute(&s,x,1));CHECK(sentinel(&s));
    mpz_ui_pow_ui(mpq_numref(x),2,255);mpz_sub_ui(mpq_denref(x),mpq_numref(x),1);
    CHECK(!weighted_remainder_spectral_mean_compute(&s,x,1));CHECK(sentinel(&s));
    /* Replacing every field consumes an aliased input before any clear. */
    for (unsigned i=0;i<28;++i) {
        mpq_set_ui(v[i],5,2);CHECK(weighted_remainder_spectral_mean_compute(&s,v[i],7));
        CHECK(s.floor_x==2 && s.prime_cutoff==7 && !mpq_cmp_ui(s.x,5,2));
        CHECK(mpq_equal(s.h_sum,s.correction_floor_sum));
    }
    mpz_ui_pow_ui(mpq_numref(x),2,254);mpz_sub_ui(mpq_denref(x),mpq_numref(x),1);
    CHECK(weighted_remainder_spectral_mean_compute(&s,x,1));CHECK(s.floor_x==1);
    weighted_remainder_spectral_mean_clear(&s);mpq_clears(a,b,x,NULL);
    tail_edges();
    printf("EDGES %u\n",edges);
}

int main(void)
{
    edge_checks();mpq_t a,b,c,d,x;mpq_inits(a,b,c,d,x,NULL);
    WeightedRemainderSpectralMean s;weighted_remainder_spectral_mean_init(&s);
    WeightedRemainderSpectralTail t;weighted_remainder_spectral_tail_init(&t);mpq_ptr tv[22];tail_fields(&t,tv);
    mpq_ptr v[28];fields(&s,v);char op;unsigned n;char input[320];
    while (scanf(" %c",&op)==1) {
        int ok;
        if (op=='T') {
            unsigned Q,B,M,P,N;if (scanf(" %u %u %u %u %u",&Q,&B,&M,&P,&N)!=5) return 2;
            ok=weighted_remainder_spectral_tail_compute(&t,Q,B,M,P,N);printf("T %d",ok);
            if (ok) {
                printf(" %u %u %u %u %u %u",t.cutoff,t.band_cutoff,t.period_cutoff,t.prime_cutoff,t.constant_cutoff,t.period_binary_exponent);
                for (unsigned i=0;i<22;++i) gmp_printf(" %Qd",tv[i]);
            }
        } else if (op=='E') {
            unsigned q,M;if (scanf(" %u %u",&q,&M)!=2) return 2;
            ok=weighted_remainder_spectral_energy_q(a,b,c,d,q,M);printf("E %d",ok);
            if (ok) gmp_printf(" %Qd %Qd %Qd %Qd",a,b,c,d);
        } else if (op=='M') {
            if (scanf(" %319s %u",input,&n)!=2 || mpq_set_str(x,input,10)) return 2;
            if (mpz_sgn(mpq_denref(x))>0) mpq_canonicalize(x);
            ok=weighted_remainder_spectral_mean_compute(&s,x,n);printf("M %d",ok);
            if (ok) {
                printf(" %u %u %u",s.floor_x,s.prime_cutoff,s.prime_tail_binary_exponent);
                for (unsigned i=0;i<28;++i) gmp_printf(" %Qd",v[i]);
            }
        } else {
            if (scanf(" %u",&n)!=1) return 2;
            if (op=='F') ok=weighted_remainder_spectral_factors_q(a,b,n);
            else if (op=='A') ok=weighted_remainder_spectral_arithmetic_q(a,b,n);
            else if (op=='P') ok=weighted_remainder_spectral_product_q(a,b,n);
            else return 2;
            printf("%c %d",op,ok);if (ok) gmp_printf(" %Qd %Qd",a,b);
        }
        putchar('\n');
    }
    weighted_remainder_spectral_mean_clear(&s);weighted_remainder_spectral_tail_clear(&t);
    mpq_clears(a,b,c,d,x,NULL);return 0;
}
