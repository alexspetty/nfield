/* Parameterized native projections. This file shares the directed interval
 * operations and complete-period Gram kernel in native_refinement.c. */
enum { DETECTOR_TOP=400, DETECTOR_DIM=401, DETECTOR_DEPTHS=7 };
typedef struct {
    Audit audit;
    unsigned top;
    Interval gram[DETECTOR_DIM][DETECTOR_DIM], mean[DETECTOR_DIM];
} NativeFrame;
/* The short-sum form of the same complete native Gram. Cache the positive
 * digamma arguments once per frame; this avoids enumerating every lcm period
 * separately when a web calculation asks for a larger projection. */
static void native_short(Interval *out,Interval table[DETECTOR_DIM][DETECTOR_DIM],unsigned n,unsigned a)
{
    Interval x;init(&x);rat(out,0,1);
    for(unsigned r=1;r<n;++r) { scale(&x,&table[n][r],(a*r)%n,n);add(out,out,&x); }
    clear(&x);
}
static void native_frame_init(NativeFrame *f,unsigned top)
{
    f->top=top;f->audit=(Audit){0,0,NULL};init_array(f->mean,DETECTOR_DIM);
    for (unsigned j=0;j<=top;++j) init_array(f->gram[j],top+1);
    Interval (*table)[DETECTOR_DIM]=malloc((top+1)*sizeof *table);
    if(!table) { check(&f->audit,0,"native Gram allocation");return; }
    Interval logs[DETECTOR_DIM],diagonal[DETECTOR_DIM],psi1,x,y,z,inner;
    init_array(logs,DETECTOR_DIM);init_array(diagonal,DETECTOR_DIM);init(&psi1);init(&x);init(&y);init(&z);init(&inner);digamma(&psi1,1,1);
    for(unsigned j=1;j<=top;++j) {
        init_array(table[j],j);rat(logs+j,j,1);mpfr_log(logs[j].lo,logs[j].lo,MPFR_RNDD);mpfr_log(logs[j].hi,logs[j].hi,MPFR_RNDU);
        for(unsigned r=1;r<j;++r)digamma(&table[j][r],r,j);
        native_short(diagonal+j,table,j,1);
    }
    for (unsigned j=2;j<=top;++j) {
        scale(f->mean+j,logs+j,1,j);
        for (unsigned k=2;k<=j;++k) {
            unsigned g=gcd(j,k),h=k/g,t=j/g;
            add(&inner,diagonal+j,diagonal+k);scale(&x,logs+h,j-1,2);sub(&inner,&inner,&x);scale(&x,logs+t,k-1,2);sub(&inner,&inner,&x);add(&inner,&inner,&psi1);add(&inner,&inner,logs+g);scale(&inner,&inner,1,g);
            native_short(&x,table,h,t%h);native_short(&y,table,t,h%t);add(&z,&x,&y);add(&z,&z,&psi1);sub(&z,&z,&inner);scale(&f->gram[j][k],&z,1,j*k/g);set(&f->gram[k][j],&f->gram[j][k]);
        }
    }
    for(unsigned j=1;j<=top;++j)clear_array(table[j],j);
    free(table);
    clear_array(logs,DETECTOR_DIM);clear_array(diagonal,DETECTOR_DIM);clear(&psi1);clear(&x);clear(&y);clear(&z);clear(&inner);
}
static void native_frame_clear(NativeFrame *f)
{
    clear_array(f->mean,DETECTOR_DIM);
    for (unsigned j=0;j<=f->top;++j) clear_array(f->gram[j],f->top+1);
}
static void native_solve(Audit *audit,unsigned n,const Interval *matrix,unsigned stride,
                         const Interval *rhs,Interval *solution)
{
    Interval (*a)[DETECTOR_DIM]=malloc(n*sizeof *a);
    if(!a) { check(audit,0,"native solve allocation");return; }
    Interval pivot,t,u;
    for (unsigned i=0;i<n;++i) init_array(a[i],n+1);
    init(&pivot);init(&t);init(&u);
    for (unsigned i=0;i<n;++i) {
        for (unsigned j=0;j<n;++j) set(&a[i][j],matrix+i*stride+j);
        set(&a[i][n],rhs+i);
    }
    for (unsigned k=0;k<n && !audit->failures;++k) {
        set(&pivot,&a[k][k]);
        for (unsigned j=k;j<=n;++j) divide(audit,&a[k][j],&a[k][j],&pivot);
        for (unsigned i=k+1;i<n;++i) {
            set(&t,&a[i][k]);
            for (unsigned j=k;j<=n;++j) { mul(&u,&t,&a[k][j]);sub(&a[i][j],&a[i][j],&u); }
        }
    }
    if (!audit->failures) for (int i=(int)n-1;i>=0;--i) {
        set(solution+i,&a[i][n]);
        for (unsigned j=(unsigned)i+1;j<n;++j) { mul(&u,&a[i][j],solution+j);sub(solution+i,solution+i,&u); }
        divide(audit,solution+i,solution+i,&a[i][i]);
    }
    for (unsigned i=0;i<n && !audit->failures;++i) {
        rat(&t,0,1);
        for (unsigned j=0;j<n;++j) { mul(&u,matrix+i*stride+j,solution+j);add(&t,&t,&u); }
        equal(audit,&t,rhs+i,"native projection original normal equation");
    }
    for (unsigned i=0;i<n;++i) clear_array(a[i],n+1);
    free(a);
    clear(&pivot);clear(&t);clear(&u);
}
static void native_projection(NativeFrame *f,unsigned N,const Interval *rhs,Interval *out)
{
    for (unsigned j=0;j<DETECTOR_DIM;++j) rat(out+j,0,1);
    native_solve(&f->audit,N-1,&f->gram[2][2],DETECTOR_DIM,rhs+2,out+2);
}
static void native_dot(Interval *out,const Interval *a,const Interval *b,unsigned top)
{
    Interval t;init(&t);rat(out,0,1);
    for (unsigned j=2;j<=top;++j) { mul(&t,a+j,b+j);add(out,out,&t); }
    clear(&t);
}
static void native_pair(NativeFrame *f,Interval *out,const Interval *a,const Interval *b)
{
    Interval t,u;init(&t);init(&u);rat(out,0,1);
    for (unsigned j=2;j<=f->top;++j) for (unsigned k=2;k<=f->top;++k) {
        mul(&t,a+j,b+k);mul(&u,&t,&f->gram[j][k]);add(out,out,&u);
    }
    clear(&t);clear(&u);
}
static void native_lift(Interval *out,const Interval *a,unsigned cutoff,unsigned s,int isometry,Audit *audit)
{
    Interval t,factor;init(&t);init(&factor);rat(&factor,s,1);
    if (isometry) root(audit,&factor,&factor);else rat(&factor,1,1);
    for (unsigned j=0;j<DETECTOR_DIM;++j) rat(out+j,0,1);
    for (unsigned j=2;j<=cutoff;++j) {
        mul(&t,a+j,&factor);add(out+s*j,out+s*j,&t);
        if (s>1) { scale(&t,&t,1,j);sub(out+s,out+s,&t); }
    }
    clear(&t);clear(&factor);
}
static void native_residual(NativeFrame *f,unsigned N,Interval *projection,Interval *Dvalue)
{
    native_projection(f,N,f->mean,projection);native_dot(Dvalue,projection,f->mean,N);
    Interval one;init(&one);rat(&one,1,1);sub(Dvalue,&one,Dvalue);clear(&one);
    check(&f->audit,mpfr_sgn(Dvalue->lo)>0,"positive native residual");
}
static void native_field(FILE *out,const char *name,const Interval *a,int json,int comma)
{
    if (json) emit(out,name,a,comma);
    else mpfr_fprintf(out,"%s=[%.20RDe, %.20RUe]\n",name,a->lo,a->hi);
}
int native_refinement_detector(unsigned N,FILE *out,int json)
{
    if (!out || N<2 || N>100) return 1;
    mpfr_prec_t saved_precision=calculation_precision;calculation_precision=N<=8?256:256+16*N;
    NativeFrame *f=calloc(1,sizeof *f);if (!f) { calculation_precision=saved_precision;return 1; }native_frame_init(f,4*N);
    Interval p[DETECTOR_DIM],fine[DETECTOR_DIM],rhs[DETECTOR_DIM],coarse[DETECTOR_DIM],detail[DETECTOR_DIM];
    Interval lifted[DETECTOR_DIM],coupling[DETECTOR_DIM],conditioner[DETECTOR_DIM],w[DETECTOR_DEPTHS][DETECTOR_DIM];
    Interval b[DETECTOR_DEPTHS],B[DETECTOR_DEPTHS],K[DETECTOR_DEPTHS][DETECTOR_DEPTHS],y[DETECTOR_DEPTHS],single_capture[DETECTOR_DEPTHS];
    Interval terminal[DETECTOR_DEPTHS],root_response[DETECTOR_DEPTHS],log_part[DETECTOR_DEPTHS],commutator_part[DETECTOR_DEPTHS];
    Interval Dvalue,Dfine,gain,J,trace,total_cost,spine,lower,t,u,sqrt2,one,zero;
    Interval *vectors[]={p,fine,rhs,coarse,detail,lifted,coupling,conditioner};
    for (unsigned i=0;i<8;++i) init_array(vectors[i],DETECTOR_DIM);
    for (unsigned h=0;h<DETECTOR_DEPTHS;++h) { init_array(w[h],DETECTOR_DIM);init_array(K[h],DETECTOR_DEPTHS); }
    init_array(single_capture,DETECTOR_DEPTHS);
    init_array(b,DETECTOR_DEPTHS);init_array(B,DETECTOR_DEPTHS);init_array(y,DETECTOR_DEPTHS);
    init_array(terminal,DETECTOR_DEPTHS);init_array(root_response,DETECTOR_DEPTHS);init_array(log_part,DETECTOR_DEPTHS);init_array(commutator_part,DETECTOR_DEPTHS);
    Interval *temps[]={&Dvalue,&Dfine,&gain,&J,&trace,&total_cost,&spine,&lower,&t,&u,&sqrt2,&one,&zero};
    for (unsigned i=0;i<13;++i) init(temps[i]);
    rat(&one,1,1);rat(&sqrt2,2,1);root(&f->audit,&sqrt2,&sqrt2);
    native_residual(f,N,p,&Dvalue);native_residual(f,4*N,fine,&Dfine);sub(&gain,&Dvalue,&Dfine);
    unsigned H=0,s=1;
    /* Determine the exact ceiling from an interval enclosing D_N. */
    while (H<20) { scale(&t,&Dvalue,s,1);if (mpfr_cmp_ui(t.lo,4)>=0) break;++H;s*=2; }
    check(&f->audit,H<20,"bounded shallow horizon");
    if (H) { scale(&t,&Dvalue,s/2,1);check(&f->audit,mpfr_cmp_ui(t.hi,4)<0,"unambiguous shallow horizon"); }
    unsigned count=0,cutoff[DETECTOR_DEPTHS],depth[DETECTOR_DEPTHS];
    for (unsigned h=0;h<H;++h) {
        unsigned scale_h=1u<<h;
        /* Literal finite support of U^h d_1, paired with the full optimizer. */
        rat(&u,0,1);
        for (unsigned n=scale_h;n<2*scale_h;++n) {
            rat(&t,1,1);
            for (unsigned j=2;j<=N;++j) { Interval v;init(&v);scale(&v,p+j,n%j,j);sub(&t,&t,&v);clear(&v); }
            scale(&t,&t,1,(unsigned long)n*(n+1));add(&u,&u,&t);
        }
        square(&t,&u);scale(&t,&t,2*scale_h,1);add(&spine,&spine,&t);
        unsigned M=N/scale_h;if (M<2) continue;
        if (!check(&f->audit,count<DETECTOR_DEPTHS,"detector depth capacity")) break;
        cutoff[count]=M;depth[count]=h;
        for (unsigned j=2;j<=4*M;++j) scale(rhs+j,&sqrt2,1,2*j);
        native_projection(f,M,rhs,coarse);native_projection(f,4*M,rhs,detail);
        for (unsigned j=2;j<=4*M;++j) sub(detail+j,detail+j,coarse+j);
        /* Schur root split: coarse projections give A*sigma and A*mu.
         * Keep the logarithmic part and the signed commutator separately. */
        native_projection(f,M,f->mean,coupling);
        Interval vr,ur,logj,term;init(&vr);init(&ur);init(&logj);init(&term);
        for(unsigned j=M+1;j<=4*M;++j) {
            native_dot(&t,f->gram[j],coarse,M);sub(&vr,rhs+j,&t);
            native_dot(&t,f->gram[j],coupling,M);sub(&ur,f->mean+j,&t);
            rat(&logj,j,1);mpfr_log(logj.lo,logj.lo,MPFR_RNDD);mpfr_log(logj.hi,logj.hi,MPFR_RNDU);
            mul(&term,&logj,&vr);mul(&t,&term,detail+j);add(log_part+count,log_part+count,&t);
            divide(&f->audit,&ur,&ur,&sqrt2);sub(&ur,&ur,&term);mul(&t,&ur,detail+j);add(commutator_part+count,commutator_part+count,&t);
        }
        clear(&vr);clear(&ur);clear(&logj);clear(&term);
        native_pair(f,B+count,detail,detail);
        native_dot(root_response+count,detail,f->mean,4*M);
        add(&t,log_part+count,commutator_part+count);mul(&t,&t,&sqrt2);equal(&f->audit,&t,root_response+count,"signed conditioning commutator");
        rat(&t,scale_h,1);root(&f->audit,&t,&t);divide(&f->audit,root_response+count,root_response+count,&t);
        native_lift(lifted,detail,4*M,scale_h,1,&f->audit);
        for (unsigned j=2;j<=N;++j) native_dot(coupling+j,f->gram[j],lifted,f->top);
        native_projection(f,N,coupling,conditioner);
        for (unsigned j=2;j<=f->top;++j) sub(w[count]+j,lifted+j,conditioner+j);
        native_dot(b+count,w[count],f->mean,f->top);native_pair(f,terminal+count,p,lifted);
        sub(&t,root_response+count,terminal+count);equal(&f->audit,&t,b+count,"signed terminal response");
        add(&total_cost,&total_cost,B+count);
        for (unsigned k=0;k<=count;++k) { native_pair(f,&K[count][k],w[count],w[k]);set(&K[k][count],&K[count][k]); }
        square(&t,b+count);divide(&f->audit,single_capture+count,&t,&K[count][count]);
        add(&trace,&trace,&K[count][count]);++count;
    }
    if (count && !f->audit.failures) {
        native_solve(&f->audit,count,&K[0][0],DETECTOR_DEPTHS,b,y);
        for (unsigned h=0;h<count;++h) { mul(&t,b+h,y+h);add(&J,&J,&t); }
    }
    square(&lower,&Dvalue);scale(&lower,&lower,1,4);
    check(&f->audit,mpfr_cmp(spine.lo,lower.hi)>0,"shallow spine forcing");
    check(&f->audit,mpfr_cmp(J.hi,gain.lo)<=0,"joint capture within available gain");
    check(&f->audit,mpfr_cmp_ui(total_cost.hi,2)<=0,"finite detector cost bound");
    int failed=f->audit.failures!=0;
    if (!failed) {
        if (json) fprintf(out,"{\"schema\":\"nfield.native-detector.v1\",\"cutoff\":%u,\"fine_cutoff\":%u,\"shallow_horizon\":%u,\"eligible_depths\":%u,\"precision_bits\":%ld,\"observation_truncation\":false,",N,4*N,H,count,(long)calculation_precision);
        else fprintf(out,"Native detector responses and complete costs\ncutoff=%u\nfine_cutoff=%u\nshallow_horizon=%u\neligible_depths=%u\n",N,4*N,H,count);
        native_field(out,"residual",&Dvalue,json,0);native_field(out,"fine_residual",&Dfine,json,1);
        native_field(out,"available_gain",&gain,json,1);native_field(out,"joint_capture",&J,json,1);
        native_field(out,"gram_trace",&trace,json,1);native_field(out,"raw_cost_sum",&total_cost,json,1);
        native_field(out,"shallow_energy",&spine,json,1);native_field(out,"shallow_lower",&lower,json,1);
        if (json) { emit_coeff(out,"optimizer",p,N);fputs(",\"probes\":[",out); }
        for (unsigned h=0;h<count;++h) {
            if (json) fprintf(out,"%s{\"depth\":%u,\"coarse_cutoff\":%u,",h?",":"",depth[h],cutoff[h]);
            else fprintf(out,"depth=%u coarse_cutoff=%u\n",depth[h],cutoff[h]);
            native_field(out,"response",b+h,json,0);native_field(out,"single_capture",single_capture+h,json,1);native_field(out,"conditioned_cost",&K[h][h],json,1);
            native_field(out,"raw_cost",B+h,json,1);native_field(out,"root_response",root_response+h,json,1);
            native_field(out,"terminal_pairing",terminal+h,json,1);
            native_field(out,"root_log_part",log_part+h,json,1);native_field(out,"root_commutator_part",commutator_part+h,json,1);
            if (json) { emit_coeff(out,"coefficients",w[h],f->top);fputc('}',out); }
        }
        if (json) {
            fputs("],\"gram\":[",out);
            for (unsigned h=0;h<count;++h) for (unsigned k=0;k<=h;++k) {
                fprintf(out,"%s{\"left\":%u,\"right\":%u,",h||k?",":"",h,k);emit(out,"value",&K[h][k],0);fputc('}',out);
            }
            fprintf(out,"],\"checks\":%u,\"failures\":0}\n",f->audit.checks);
        } else fputs("Directed intervals in the complete native norm. These finite detector gains do not establish a divergent capture budget.\n",out);
    } else fprintf(stderr,"native detector: %s\n",f->audit.first_error);
    for (unsigned i=0;i<8;++i) clear_array(vectors[i],DETECTOR_DIM);
    for (unsigned h=0;h<DETECTOR_DEPTHS;++h) { clear_array(w[h],DETECTOR_DIM);clear_array(K[h],DETECTOR_DEPTHS); }
    clear_array(single_capture,DETECTOR_DEPTHS);
    clear_array(b,DETECTOR_DEPTHS);clear_array(B,DETECTOR_DEPTHS);clear_array(y,DETECTOR_DEPTHS);
    clear_array(terminal,DETECTOR_DEPTHS);clear_array(root_response,DETECTOR_DEPTHS);clear_array(log_part,DETECTOR_DEPTHS);clear_array(commutator_part,DETECTOR_DEPTHS);
    for (unsigned i=0;i<13;++i) clear(temps[i]);
    native_frame_clear(f);free(f);
    mpfr_free_cache2(MPFR_FREE_LOCAL_CACHE);calculation_precision=saved_precision;return failed;
}

static int native_packet(unsigned t,FILE *out,int json)
{
    if(t<2||t>4||!out)return 1;
    NativeFrame *f=calloc(1,sizeof *f);if(!f)return 1;
    native_frame_init(f,16*t);
    mpq_t coeff[DETECTOR_DIM];for(unsigned j=0;j<DETECTOR_DIM;++j)mpq_init(coeff[j]);
    Interval p[DETECTOR_DIM],q[DETECTOR_DIM],copy[DETECTOR_DIM],change[DETECTOR_DIM];
    init_array(p,DETECTOR_DIM);init_array(q,DETECTOR_DIM);init_array(copy,DETECTOR_DIM);init_array(change,DETECTOR_DIM);
    check(&f->audit,native_packet_coefficients(coeff,DETECTOR_DIM,t),"packet coefficients");for(unsigned j=0;j<=8*t;++j)from_q(p+j,coeff[j]);
    check(&f->audit,native_packet_coefficients(coeff,DETECTOR_DIM,2*t),"child packet coefficients");for(unsigned j=0;j<=16*t;++j)from_q(q+j,coeff[j]);
    native_lift(copy,p,8*t,2,0,&f->audit);
    for(unsigned j=0;j<DETECTOR_DIM;++j)sub(change+j,q+j,copy+j);
    Interval E,E2,eta,pair,S,boundary,x,y,upper;Interval *v[]={&E,&E2,&eta,&pair,&S,&boundary,&x,&y,&upper};for(unsigned i=0;i<9;++i)init(v[i]);
    native_pair(f,&E,p,p);native_pair(f,&E2,q,q);rat(&boundary,3,2);sub(&E,&E,&boundary);sub(&E2,&E2,&boundary);
    native_pair(f,&eta,change,change);rat(&x,13,4);sub(&eta,&eta,&x);
    native_pair(f,&pair,copy,change);rat(&x,5,4);add(&pair,&pair,&x);
    scale(&S,&pair,2,1);add(&S,&S,&eta);scale(&x,&E,1,2);add(&x,&x,&S);equal(&f->audit,&x,&E2,"complete packet work including boundary");
    for(unsigned n=1;n<=4*t;++n) {
        rat(&x,0,1);for(unsigned j=2;j<=8*t;++j) { scale(&y,p+j,n%j,j);add(&x,&x,&y); }
        rat(&y,n==1?-1:(n==2||n==3?2:0),1);equal(&f->audit,&x,&y,"exact packet boundary and vanished prefix");
    }
    rat(&upper,36*(54*t+9),1);check(&f->audit,mpfr_cmp(E.hi,upper.lo)<=0,"global packet envelope");
    int failed=f->audit.failures!=0;
    if(!failed) {
        if(json)fprintf(out,"{\"schema\":\"nfield.native-packet.v1\",\"scale\":%u,\"fine_scale\":%u,\"observation_truncation\":false,",t,2*t);
        else fprintf(out,"Complete tapered-packet work\nscale=%u\nfine_scale=%u\n",t,2*t);
        native_field(out,"energy",&E,json,0);native_field(out,"fine_energy",&E2,json,1);native_field(out,"new_field_energy",&eta,json,1);native_field(out,"old_new_pairing",&pair,json,1);native_field(out,"signed_work",&S,json,1);native_field(out,"fixed_boundary_energy",&boundary,json,1);native_field(out,"global_energy_upper",&upper,json,1);
        if(json) { emit_coeff(out,"coefficients",p,8*t);emit_coeff(out,"fine_coefficients",q,16*t);fprintf(out,",\"checks\":%u,\"failures\":0}\n",f->audit.checks); }
        else puts("The complete norm includes every address. The upper bound uses the global arithmetic envelope <=1, not a finite-prefix estimate.");
    }
    for(unsigned i=0;i<9;++i)clear(v[i]);
    for(unsigned j=0;j<DETECTOR_DIM;++j)mpq_clear(coeff[j]);
    clear_array(p,DETECTOR_DIM);clear_array(q,DETECTOR_DIM);clear_array(copy,DETECTOR_DIM);clear_array(change,DETECTOR_DIM);native_frame_clear(f);free(f);mpfr_free_cache2(MPFR_FREE_LOCAL_CACHE);return failed;
}

static int native_copy_cost(unsigned q,unsigned count,FILE *out)
{
    if(q<2||q>10000||count<1||count>10000||!out)return 1;
    Audit audit={0,0,NULL};Interval rho,power,cost,sum,x,y,one;
    Interval *v[]={&rho,&power,&cost,&sum,&x,&y,&one};for(unsigned i=0;i<7;++i)init(v[i]);
    rat(&one,1,1);rat(&rho,q,1);root(&audit,&rho,&rho);divide(&audit,&rho,&one,&rho);
    add(&x,&one,&rho);sub(&y,&one,&rho);divide(&audit,&cost,&x,&y);set(&sum,&one);set(&power,&one);
    for(unsigned d=1;d<count;++d) { mul(&power,&power,&rho);scale(&x,&power,2L*(count-d),count);add(&sum,&sum,&x); }
    native_field(out,"neighbor_overlap",&rho,0,0);native_field(out,"universal_synthesis_bound",&cost,0,0);native_field(out,"constant_mask_equal_weight_energy",&sum,0,0);
    for(unsigned i=0;i<7;++i)clear(v[i]);
    return audit.failures!=0;
}

static int native_kernel(unsigned j,unsigned k,FILE *out)
{
    if(j<2||k<2||j>64||k>64||!out)return 1;
    NativeFrame *f=calloc(1,sizeof *f);if(!f)return 1;native_frame_init(f,j>k?j:k);
    Interval direct;init(&direct);gram_entry(&direct,j,k);equal(&f->audit,&direct,&f->gram[j][k],"independent complete-period Gram");
    int failed=f->audit.failures!=0;
    if(!failed) { native_field(out,"complete_period",&direct,0,0);native_field(out,"short_sum",&f->gram[j][k],0,0); }
    clear(&direct);native_frame_clear(f);free(f);mpfr_free_cache2(MPFR_FREE_LOCAL_CACHE);return failed;
}

static int native_transport(unsigned N,FILE *out,int json)
{
    if(N<2||N>8||!out)return 1;
    NativeFrame *f=calloc(1,sizeof *f);if(!f)return 1;native_frame_init(f,2*N);
    Interval p[DETECTOR_DIM],q[DETECTOR_DIM],copy[DETECTOR_DIM],difference[DETECTOR_DIM];
    init_array(p,DETECTOR_DIM);init_array(q,DETECTOR_DIM);init_array(copy,DETECTOR_DIM);init_array(difference,DETECTOR_DIM);
    Interval D,D2,gain,norm,x,y,value,mean;Interval *v[]={&D,&D2,&gain,&norm,&x,&y,&value,&mean};for(unsigned i=0;i<8;++i)init(v[i]);
    native_residual(f,N,p,&D);native_residual(f,2*N,q,&D2);native_lift(copy,p,N,2,0,&f->audit);
    for(unsigned j=2;j<=2*N;++j)sub(difference+j,copy+j,q+j);
    /* r_(2N)-T r_N = delta_1 + T p_N-p_(2N). */
    native_pair(f,&norm,difference,difference);rat(&x,1,2);add(&norm,&norm,&x);
    for(unsigned j=2;j<=2*N;++j) { scale(&x,difference+j,1,j);add(&norm,&norm,&x); }
    sub(&gain,&D,&D2);scale(&value,&D,1,2);native_dot(&mean,difference,f->mean,2*N);rat(&x,1,2);add(&mean,&mean,&x);
    int failed=f->audit.failures!=0;
    if(!failed) {
    if(json)fprintf(out,"{\"schema\":\"nfield.native-transport.v1\",\"cutoff\":%u,",N);else fprintf(out,"Native dilation and refitting\ncutoff=%u\n",N);
    native_field(out,"residual",&D,json,0);native_field(out,"fine_residual",&D2,json,1);native_field(out,"projection_gain",&gain,json,1);native_field(out,"copied_residual_energy",&value,json,1);native_field(out,"refitting_correction_energy",&norm,json,1);native_field(out,"correction_unity_pairing",&mean,json,1);
    if(json) { emit_coeff(out,"correction_clock_coefficients",difference,2*N);fputs(",\"origin_coefficient\":1,\"failures\":0}\n",out); }
    else fputs("The correction includes the origin delta and the changed optimizer.\n",out);
    } else fprintf(stderr,"native transport: %s\n",f->audit.first_error);
    for(unsigned i=0;i<8;++i)clear(v[i]);
    clear_array(p,DETECTOR_DIM);clear_array(q,DETECTOR_DIM);clear_array(copy,DETECTOR_DIM);clear_array(difference,DETECTOR_DIM);native_frame_clear(f);free(f);mpfr_free_cache2(MPFR_FREE_LOCAL_CACHE);return failed;
}
