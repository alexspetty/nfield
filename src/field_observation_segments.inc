/* Piecewise affine observations with independent boundary readings. */
static void segment_value(Complex *out,const mpq_t x,Complex data[4][FO_FIELDS],unsigned n)
{
    unsigned i=0;while(i+1<n&&mpq_cmp(data[0][i+1].re,x)<=0)++i;
    if(mpq_equal(x,data[0][i].re)) { zs(out,data[3]+i);return; }
    mpq_t t;mpq_init(t);mpq_sub(t,x,data[0][i].re);zq(out,data[2]+i,t);za(out,out,data[1]+i);mpq_clear(t);
}
static void bernoulli(mpq_t out,const mpq_t x,unsigned degree)
{
    mpq_t f,t;mpq_inits(f,t,NULL);fraction(f,x);mpq_mul(out,f,f);
    if(degree==2) { mpq_sub(out,out,f);qi(t,1,6);mpq_add(out,out,t); }
    else { qs(t,out,3,2);mpq_mul(out,out,f);mpq_sub(out,out,t);qs(t,f,1,2);mpq_add(out,out,t); }
    mpq_clears(f,t,NULL);
}
static int segments(int argc,char **argv)
{
    if(argc!=7)return 1;
    unsigned q=0,n=0,k=0;Complex d[4][FO_FIELDS],value,previous,z;
    for(unsigned i=0;i<4;++i)for(unsigned j=0;j<FO_FIELDS;++j)zi(&d[i][j]);
    zi(&value);zi(&previous);zi(&z);
    mpq_t theta,x,y,t,h,w,continuous,sample,point,jump,derivative,regular,defect,error;
    mpq_inits(theta,x,y,t,h,w,continuous,sample,point,jump,derivative,regular,defect,error,NULL);
    int ok=integer(argv[1],&q,10000)&&q&&rational(argv[2],theta)&&mpq_sgn(theta)>=0&&mpq_cmp_ui(theta,1,1)<0;
    for(unsigned i=0;i<4&&ok;++i) { ok=list(argv[i+3],d[i],FO_FIELDS,&k);if(!i)n=k;else ok=ok&&n==k; }
    ok=ok&&real_list(d[0],n,0)&&!mpq_sgn(d[0][0].re);
    for(unsigned i=0;i<n&&ok;++i)ok=mpq_cmp_ui(d[0][i].re,1,1)<0&&(!i||mpq_cmp(d[0][i-1].re,d[0][i].re)<0);
    if(ok) {
        for(unsigned i=0;i<n;++i) {
            if(i+1<n)mpq_set(y,d[0][i+1].re);else qi(y,1,1);
            mpq_sub(w,y,d[0][i].re);qs(x,w,1,2);zq(&value,d[2]+i,x);za(&value,&value,d[1]+i);
            zn(h,&value);zn(t,d[2]+i);mpq_mul(x,w,w);mpq_mul(x,x,t);qs(x,x,1,12);mpq_add(h,h,x);mpq_mul(h,h,w);mpq_add(continuous,continuous,h);
            qs(y,y,q,1);mpq_sub(y,y,theta);bernoulli(h,y,3);qs(x,d[0][i].re,q,1);mpq_sub(x,x,theta);bernoulli(y,x,3);mpq_sub(h,h,y);mpq_mul(h,h,t);qs(h,h,1,3UL*q*q*q);mpq_add(regular,regular,h);
        }
        for(unsigned a=0;a<q;++a) { qi(x,a,1);mpq_add(x,x,theta);qs(x,x,1,q);segment_value(&value,x,d,n);zn(h,&value);qs(h,h,1,q);mpq_add(sample,sample,h); }
        for(unsigned i=0;i<n;++i) {
            unsigned j=i?i-1:n-1;if(i)mpq_set(w,d[0][i].re);else qi(w,1,1);mpq_sub(w,w,d[0][j].re);zq(&previous,d[2]+j,w);za(&previous,&previous,d[1]+j);
            qs(x,d[0][i].re,q,1);mpq_sub(x,x,theta);
            zn(h,&previous);zn(y,d[1]+i);
            if(whole(x)) { mpq_add(t,h,y);qs(t,t,1,2);zn(w,d[3]+i);mpq_sub(t,t,w);qs(t,t,1,q);mpq_add(point,point,t); }
            mpq_sub(t,y,h);saw(w,x);mpq_mul(t,t,w);qs(t,t,-1,q);mpq_add(jump,jump,t);
            zm(&z,d[1]+i,d[2]+i,1);mpq_set(t,z.re);zm(&z,&previous,d[2]+j,1);mpq_sub(t,t,z.re);bernoulli(w,x,2);mpq_mul(t,t,w);qs(t,t,1,(unsigned long)q*q);mpq_add(derivative,derivative,t);
        }
        mpq_sub(defect,continuous,sample);mpq_add(error,point,jump);mpq_add(error,error,derivative);mpq_add(error,error,regular);mpq_sub(error,error,defect);ok=!mpq_sgn(error);
        if(ok) { qp("continuous_energy",continuous);qp("sampled_energy",sample);qp("defect",defect);qp("point_correction",point);qp("value_jump",jump);qp("derivative_jump",derivative);qp("regular_curvature",regular);qp("identity_error",error); }
    }
    for(unsigned i=0;i<4;++i)for(unsigned j=0;j<FO_FIELDS;++j)zc(&d[i][j]);
    zc(&value);zc(&previous);zc(&z);
    mpq_clears(theta,x,y,t,h,w,continuous,sample,point,jump,derivative,regular,defect,error,NULL);return !ok;
}
static int tail_bound(int argc,char **argv)
{
    if(argc!=5&&argc!=6)return 1;
    unsigned N=0;mpq_t A,C,H,x,y,t;mpq_inits(A,C,H,x,y,t,NULL);
    int ok=integer(argv[1],&N,1000000)&&rational(argv[2],A)&&rational(argv[3],C)&&rational(argv[4],H)&&mpq_sgn(A)>=0&&mpq_sgn(C)>=0;
    if(argc==6)ok=ok&&rational(argv[5],t)&&mpq_sgn(t)>0;
    if(ok) {
        mpq_mul(A,A,A);mpq_mul(C,C,C);qs(x,A,1,N+1);qs(y,C,1,N+1);mpq_sub(x,H,x);mpq_add(y,H,y);qp("complete_change_lower",x);qp("complete_change_upper",y);
        if(argc==6) { mpq_div(x,mpq_cmp(A,C)>0?A:C,t);mpz_t cutoff;mpz_init(cutoff);mpz_cdiv_q(cutoff,mpq_numref(x),mpq_denref(x));if(mpz_sgn(cutoff)>0)mpz_sub_ui(cutoff,cutoff,1);if(mpz_cmp_ui(cutoff,N)<0)mpz_set_ui(cutoff,N);gmp_printf("sufficient_cutoff=%Zd\n",cutoff);mpz_clear(cutoff); }
        puts("Conditional on the supplied envelopes holding throughout the omitted native tail.");
    }
    mpq_clears(A,C,H,x,y,t,NULL);return !ok;
}
static int native_cycle(int argc,char **argv)
{
    if(argc!=3)return 1;
    unsigned N=0,P=0;Complex values[FO_VALUES];for(unsigned i=0;i<FO_VALUES;++i)zi(values+i);
    int ok=integer(argv[1],&N,1000000)&&list(argv[2],values,FO_VALUES,&P);
    mpq_t norm;mpq_init(norm);mpfr_t lo,hi,x,y,a,b,wlo,whi,z;
    mpfr_inits2(256,lo,hi,x,y,a,b,wlo,whi,z,(mpfr_ptr)0);mpfr_set_zero(lo,0);mpfr_set_zero(hi,0);
    if(ok)for(unsigned r=0;r<P;++r) {
        unsigned first=N+1+(r+P-(N+1)%P)%P;
        mpfr_set_ui(a,first,MPFR_RNDN);mpfr_div_ui(x,a,P,MPFR_RNDD);mpfr_div_ui(y,a,P,MPFR_RNDU);
        mpfr_digamma(a,x,MPFR_RNDD);mpfr_digamma(b,y,MPFR_RNDU);
        mpfr_set_ui(z,first+1,MPFR_RNDN);mpfr_div_ui(x,z,P,MPFR_RNDD);mpfr_div_ui(y,z,P,MPFR_RNDU);
        mpfr_digamma(wlo,x,MPFR_RNDD);mpfr_digamma(whi,y,MPFR_RNDU);mpfr_sub(wlo,wlo,b,MPFR_RNDD);mpfr_sub(whi,whi,a,MPFR_RNDU);mpfr_div_ui(wlo,wlo,P,MPFR_RNDD);mpfr_div_ui(whi,whi,P,MPFR_RNDU);
        zn(norm,values+r);mpfr_set_q(x,norm,MPFR_RNDD);mpfr_set_q(y,norm,MPFR_RNDU);mpfr_mul(wlo,wlo,x,MPFR_RNDD);mpfr_mul(whi,whi,y,MPFR_RNDU);mpfr_add(lo,lo,wlo,MPFR_RNDD);mpfr_add(hi,hi,whi,MPFR_RNDU);
    }
    if(ok)mpfr_printf("complete_energy=[%.20RDe, %.20RUe]\nperiod=%u\ncutoff=%u\nComplete native tail; list entry zero is the residue-zero reading.\n",lo,hi,P,N);
    mpfr_clears(lo,hi,x,y,a,b,wlo,whi,z,(mpfr_ptr)0);mpq_clear(norm);for(unsigned i=0;i<FO_VALUES;++i)zc(values+i);mpfr_free_cache2(MPFR_FREE_LOCAL_CACHE);return !ok;
}
