#include "../src/weighted_remainder_fourier.h"
#include "../src/weighted_remainder_weights.h"
#include "../src/weighted_remainder_rows.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static unsigned edges;
#define CHECK(x) do { ++edges;if (!(x)) { fprintf(stderr,"edge failed line %d: %s\n",__LINE__,#x);exit(1); } } while (0)

static void trig_fields(WeightedRemainderTrig *s,mpq_ptr *v)
{
    mpq_ptr a[]={s->sin_lower,s->sin_upper,s->cos_lower,s->cos_upper,
        s->cot_lower,s->cot_upper,s->csc_squared_lower,s->csc_squared_upper};
    memcpy(v,a,sizeof a);
}

static void fields(WeightedRemainderFourier *s,mpq_ptr *v)
{
    mpq_ptr a[]={s->amplitude_lower,s->amplitude_upper,s->g_lower,s->g_upper,
        s->y_real_lower,s->y_real_upper,s->y_imag_lower,s->y_imag_upper,
        s->g_mass_lower,s->g_mass_upper,s->y_mass_lower,s->y_mass_upper};
    memcpy(v,a,sizeof a);trig_fields(&s->trig,v+12);
}

static int equal(WeightedRemainderFourier *s,WeightedRemainderFourier *t)
{
    if (s->mode!=t->mode || s->cutoff!=t->cutoff || s->trig.conductor!=t->trig.conductor ||
        s->trig.residue!=t->trig.residue) return 0;
    mpq_ptr a[20],b[20];fields(s,a);fields(t,b);
    for (unsigned i=0;i<20;++i) if (!mpq_equal(a[i],b[i])) return 0;
    return 1;
}

static void profile(mpq_t *v,unsigned M,unsigned kind)
{
    for (unsigned k=0;k<=M;++k) {
        mpq_set_ui(v[k],0,1);if (k<2) continue;
        if (kind==1) weighted_remainder_weight_q(v[k],k);
        else if (kind==2) { mpq_set_si(v[k],k%2 ? -1 : 1,k+1);mpq_canonicalize(v[k]); }
        else if (kind==3 && k==M) mpq_set_ui(v[k],1,1);
        else if (kind==4 && (k==2 || k==3 || k==5)) mpq_set_si(v[k],k==3 ? -7 : 2,11);
    }
}

static void edge_checks(void)
{
    WeightedRemainderFourier s,t;weighted_remainder_fourier_init(&s);weighted_remainder_fourier_init(&t);
    mpq_t lo,hi,v[241];mpq_inits(lo,hi,NULL);
    for (unsigned k=0;k<=240;++k) mpq_init(v[k]);
    mpz_t z;mpz_init_set_si(z,-1);
    mpq_set_si(lo,-3,2);mpq_set_ui(hi,5,7);
    CHECK(weighted_remainder_fourier_interval_compute(&t,239,z,lo,hi));
    mpq_ptr sf[20],tf[20];fields(&s,sf);fields(&t,tf);
    for (unsigned i=0;i<20;++i) {
        mpq_set(sf[i],lo);
        CHECK(weighted_remainder_fourier_interval_compute(&s,239,z,sf[i],hi));CHECK(equal(&s,&t));
        mpq_set(sf[i],hi);
        CHECK(weighted_remainder_fourier_interval_compute(&s,239,z,lo,sf[i]));CHECK(equal(&s,&t));
        mpz_set_si(mpq_numref(sf[i]),-1);
        CHECK(weighted_remainder_fourier_interval_compute(&s,239,mpq_numref(sf[i]),lo,hi));CHECK(equal(&s,&t));
        mpz_set_si(mpq_denref(sf[i]),-1);
        CHECK(weighted_remainder_fourier_interval_compute(&s,239,mpq_denref(sf[i]),lo,hi));CHECK(equal(&s,&t));
    }
    CHECK(!weighted_remainder_fourier_interval_compute(&s,1,z,lo,hi));CHECK(equal(&s,&t));
    CHECK(!weighted_remainder_fourier_interval_compute(&s,241,z,lo,hi));CHECK(equal(&s,&t));
    CHECK(!weighted_remainder_fourier_interval_compute(&s,239,z,hi,lo));CHECK(equal(&s,&t));
    mpz_set_ui(mpq_numref(lo),2);mpz_set_ui(mpq_denref(lo),4);
    CHECK(!weighted_remainder_fourier_interval_compute(&s,239,z,lo,hi));CHECK(equal(&s,&t));
    mpz_set_si(mpq_denref(lo),-4);
    CHECK(!weighted_remainder_fourier_interval_compute(&s,239,z,lo,hi));CHECK(equal(&s,&t));
    mpz_set_ui(mpq_denref(lo),0);
    CHECK(!weighted_remainder_fourier_interval_compute(&s,239,z,lo,hi));CHECK(equal(&s,&t));
    mpq_set_si(lo,-3,2);mpz_set_ui(z,2);
    CHECK(!weighted_remainder_fourier_interval_compute(&s,6,z,lo,hi));CHECK(equal(&s,&t));
    mpz_set_ui(z,0);
    CHECK(!weighted_remainder_fourier_interval_compute(&s,239,z,lo,hi));CHECK(equal(&s,&t));
    mpz_set_si(z,-1);
    CHECK(!weighted_remainder_fourier_collision_compute(&s,1,239,z,1));CHECK(equal(&s,&t));
    CHECK(!weighted_remainder_fourier_collision_compute(&s,241,239,z,1));CHECK(equal(&s,&t));
    CHECK(!weighted_remainder_fourier_collision_compute(&s,240,239,z,2));CHECK(equal(&s,&t));
    CHECK(!weighted_remainder_fourier_finite_compute(&s,1,239,z,v));CHECK(equal(&s,&t));
    CHECK(!weighted_remainder_fourier_finite_compute(&s,241,239,z,v));CHECK(equal(&s,&t));
    mpq_set_ui(v[1],1,1);
    CHECK(!weighted_remainder_fourier_finite_compute(&s,12,239,z,v));CHECK(equal(&s,&t));
    mpq_set_ui(v[1],0,1);mpz_set_ui(mpq_numref(v[3]),2);mpz_set_ui(mpq_denref(v[3]),4);
    CHECK(!weighted_remainder_fourier_finite_compute(&s,12,239,z,v));CHECK(equal(&s,&t));
    mpq_set_ui(v[3],0,1);
    CHECK(!weighted_remainder_fourier_finite_compute(&s,12,239,z,NULL));CHECK(equal(&s,&t));
    CHECK(!weighted_remainder_fourier_interval_compute(NULL,239,z,lo,hi));
    CHECK(!weighted_remainder_fourier_collision_compute(NULL,12,239,z,1));
    CHECK(!weighted_remainder_fourier_finite_compute(NULL,12,239,z,v));
    CHECK(!weighted_remainder_trig_compute(NULL,239,z));
    WeightedRemainderTrig tr,ref;weighted_remainder_trig_init(&tr);weighted_remainder_trig_init(&ref);
    mpq_ptr trf[8],rf[8];trig_fields(&tr,trf);trig_fields(&ref,rf);
    CHECK(weighted_remainder_trig_compute(&ref,239,z));
    for (unsigned i=0;i<8;++i) for (unsigned limb=0;limb<2;++limb) {
        mpz_ptr phase=limb ? mpq_denref(trf[i]) : mpq_numref(trf[i]);mpz_set_si(phase,-1);
        CHECK(weighted_remainder_trig_compute(&tr,239,phase));
        int same=tr.residue==ref.residue && tr.conductor==ref.conductor;
        for (unsigned j=0;j<8;++j) same &= mpq_equal(trf[j],rf[j]);
        CHECK(same);
    }
    CHECK(!weighted_remainder_trig_compute(&tr,1,z));CHECK(!weighted_remainder_trig_compute(&tr,241,z));
    mpz_set_ui(z,0);CHECK(!weighted_remainder_trig_compute(&tr,239,z));mpz_set_si(z,-1);
    for (unsigned j=0;j<8;++j) CHECK(mpq_equal(trf[j],rf[j]));
    mpq_t row[4],rr[4];for (unsigned i=0;i<4;++i) { mpq_init(row[i]);mpq_init(rr[i]); }
    CHECK(weighted_remainder_row_fourier_q(rr[0],rr[1],rr[2],rr[3],239,239,z));
    for (unsigned i=0;i<4;++i) for (unsigned limb=0;limb<2;++limb) {
        mpz_ptr phase=limb ? mpq_denref(row[i]) : mpq_numref(row[i]);mpz_set_si(phase,-1);
        CHECK(weighted_remainder_row_fourier_q(row[0],row[1],row[2],row[3],239,239,phase));
        for (unsigned j=0;j<4;++j) CHECK(mpq_equal(row[j],rr[j]));
    }
    for (unsigned i=0;i<4;++i) for (unsigned j=0;j<i;++j) {
        mpq_ptr args[4]={row[0],row[1],row[2],row[3]};args[i]=args[j];
        CHECK(!weighted_remainder_row_fourier_q(args[0],args[1],args[2],args[3],239,239,z));
        for (unsigned k=0;k<4;++k) CHECK(mpq_equal(row[k],rr[k]));
    }
    CHECK(!weighted_remainder_row_fourier_q(row[0],row[1],row[2],row[3],1,239,z));
    CHECK(!weighted_remainder_row_fourier_q(row[0],row[1],row[2],row[3],241,239,z));
    for (unsigned j=0;j<4;++j) CHECK(mpq_equal(row[j],rr[j]));
    /* Signed phase overlap also survives the finite-array wrapper. */
    profile(v,20,2);
    CHECK(weighted_remainder_fourier_finite_compute(&t,20,7,z,v));
    CHECK(weighted_remainder_fourier_finite_compute(&s,20,7,z,v));CHECK(equal(&s,&t));
    for (unsigned i=0;i<20;++i) {
        mpz_set_si(mpq_numref(sf[i]),-1);
        CHECK(weighted_remainder_fourier_finite_compute(&s,20,7,mpq_numref(sf[i]),v));CHECK(equal(&s,&t));
    }
    for (unsigned i=0;i<4;++i) { mpq_clear(row[i]);mpq_clear(rr[i]); }
    weighted_remainder_trig_clear(&tr);weighted_remainder_trig_clear(&ref);
    for (unsigned k=0;k<=240;++k) mpq_clear(v[k]);
    mpq_clears(lo,hi,NULL);mpz_clear(z);weighted_remainder_fourier_clear(&s);weighted_remainder_fourier_clear(&t);
    printf("EDGES %u\n",edges);
}

int main(void)
{
    edge_checks();
    WeightedRemainderFourier s;weighted_remainder_fourier_init(&s);
    WeightedRemainderTrig t;weighted_remainder_trig_init(&t);
    WeightedRemainderRows row;weighted_remainder_rows_init(&row);
    mpq_t lo,hi,v[241],rr[4];mpq_inits(lo,hi,NULL);
    for (unsigned k=0;k<=240;++k) mpq_init(v[k]);
    for (unsigned k=0;k<4;++k) mpq_init(rr[k]);
    mpz_t z;mpz_init(z);
    char line[4096];
    while (fgets(line,sizeof line,stdin)) {
        char *a[8];unsigned n=0;char *p=strtok(line," \t\r\n");
        while (p && n<8) { a[n++]=p;p=strtok(NULL," \t\r\n"); }
        if (!n) continue;
        char op=a[0][0];unsigned q=n>1 ? (unsigned)strtoul(a[1],NULL,10) : 0;
        int ok=0;mpq_ptr out[20];unsigned count=0;
        if (op=='T' && n==3) {
            mpz_set_str(z,a[2],10);ok=weighted_remainder_trig_compute(&t,q,z);
            printf("T %d",ok);if (ok) { printf(" %u %u",t.conductor,t.residue);trig_fields(&t,out);count=8; }
        } else if ((op=='C' || op=='F') && n==5) {
            unsigned M=q;q=(unsigned)strtoul(a[2],NULL,10);mpz_set_str(z,a[3],10);
            unsigned kind=(unsigned)strtoul(a[4],NULL,10);
            if (op=='C') ok=weighted_remainder_fourier_collision_compute(&s,M,q,z,(int)kind);
            else { if (M<=240) profile(v,M,kind);ok=weighted_remainder_fourier_finite_compute(&s,M,q,z,v); }
            printf("%c %d",op,ok);if (ok) { printf(" %u %u %u %u",s.mode,s.cutoff,s.trig.conductor,s.trig.residue);fields(&s,out);count=20; }
        } else if (op=='I' && n==5) {
            mpz_set_str(z,a[2],10);mpq_set_str(lo,a[3],10);mpq_canonicalize(lo);
            mpq_set_str(hi,a[4],10);mpq_canonicalize(hi);
            ok=weighted_remainder_fourier_interval_compute(&s,q,z,lo,hi);
            printf("I %d",ok);if (ok) { printf(" %u %u %u %u",s.mode,s.cutoff,s.trig.conductor,s.trig.residue);fields(&s,out);count=20; }
        } else if (op=='R' && n==4) {
            unsigned p=q;q=(unsigned)strtoul(a[2],NULL,10);mpz_set_str(z,a[3],10);
            ok=weighted_remainder_row_fourier_q(rr[0],rr[1],rr[2],rr[3],p,q,z);
            printf("R %d",ok);if (ok) { for (unsigned k=0;k<4;++k) out[k]=rr[k];count=4; }
        } else if (op=='V' && n==2 && q>=2 && q<=240) {
            printf("V 1");
            for (unsigned j=0;j<q;++j) {
                mpz_set_ui(z,j);if (!weighted_remainder_rows_compute(&row,q,z)) return 2;
                gmp_printf(" %Qd %Qd %Qd",row.primitive,row.odd,row.ramanujan);
            }
        } else { fputs("bad test query\n",stderr);return 2; }
        for (unsigned k=0;k<count;++k) gmp_printf(" %Qd",out[k]);
        putchar('\n');
    }
    for (unsigned k=0;k<=240;++k) mpq_clear(v[k]);
    for (unsigned k=0;k<4;++k) mpq_clear(rr[k]);
    mpq_clears(lo,hi,NULL);mpz_clear(z);weighted_remainder_rows_clear(&row);
    weighted_remainder_trig_clear(&t);weighted_remainder_fourier_clear(&s);return 0;
}
