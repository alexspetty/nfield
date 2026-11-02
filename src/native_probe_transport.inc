/* Fourfold transport of the prescribed conditioned probes. Each new probe
 * is built from its definition and independently from the old probe. */
static void native_conditioned_probe(NativeFrame *f,unsigned N,unsigned depth,Interval *out)
{
    unsigned scale_h=1u<<depth,M=N/scale_h;
    Interval rhs[DETECTOR_DIM],coarse[DETECTOR_DIM],detail[DETECTOR_DIM];
    Interval lifted[DETECTOR_DIM],coupling[DETECTOR_DIM],conditioner[DETECTOR_DIM],sqrt2;
    Interval *vectors[]={rhs,coarse,detail,lifted,coupling,conditioner};
    for(unsigned i=0;i<6;++i)init_array(vectors[i],DETECTOR_DIM);
    init(&sqrt2);rat(&sqrt2,2,1);root(&f->audit,&sqrt2,&sqrt2);
    for(unsigned j=2;j<=4*M;++j)scale(rhs+j,&sqrt2,1,2*j);
    native_projection(f,M,rhs,coarse);native_projection(f,4*M,rhs,detail);
    for(unsigned j=2;j<=4*M;++j)sub(detail+j,detail+j,coarse+j);
    native_lift(lifted,detail,4*M,scale_h,1,&f->audit);
    for(unsigned j=2;j<=N;++j)native_dot(coupling+j,f->gram[j],lifted,f->top);
    native_projection(f,N,coupling,conditioner);
    for(unsigned j=0;j<=f->top;++j)sub(out+j,lifted+j,conditioner+j);
    clear(&sqrt2);for(unsigned i=0;i<6;++i)clear_array(vectors[i],DETECTOR_DIM);
}

static unsigned native_shallow_horizon(NativeFrame *f,const Interval *residual)
{
    unsigned H=0,scale_h=1;Interval x;init(&x);
    while(H<20) {
        scale(&x,residual,scale_h,1);
        if(mpfr_cmp_ui(x.lo,4)>=0)break;
        ++H;scale_h*=2;
    }
    check(&f->audit,H<20,"bounded transport shallow horizon");
    if(H) { scale(&x,residual,scale_h/2,1);check(&f->audit,mpfr_cmp_ui(x.hi,4)<0,"unambiguous transport shallow horizon"); }
    clear(&x);return H;
}

int native_refinement_probe_transport(unsigned N,FILE *out,int json)
{
    if(!out||N<2||N>8)return 1;
    mpfr_prec_t saved_precision=calculation_precision;calculation_precision=256+64*N;
    NativeFrame *f=calloc(1,sizeof *f);
    if(!f) { calculation_precision=saved_precision;return 1; }
    native_frame_init(f,16*N);
    Interval old[DETECTOR_DEPTHS][DETECTOR_DIM],next[DETECTOR_DEPTHS][DETECTOR_DIM];
    Interval removed[DETECTOR_DEPTHS][DETECTOR_DIM];
    Interval old_gram[DETECTOR_DEPTHS][DETECTOR_DEPTHS],new_gram[DETECTOR_DEPTHS][DETECTOR_DEPTHS],loss[DETECTOR_DEPTHS][DETECTOR_DEPTHS];
    Interval old_response[DETECTOR_DEPTHS],new_response[DETECTOR_DEPTHS],drift[DETECTOR_DEPTHS];
    Interval p[DETECTOR_DIM],q[DETECTOR_DIM],lifted[DETECTOR_DIM],coupling[DETECTOR_DIM];
    Interval Dvalue,Dnext,x,y,zero;
    for(unsigned i=0;i<DETECTOR_DEPTHS;++i) {
        init_array(old[i],DETECTOR_DIM);init_array(next[i],DETECTOR_DIM);init_array(removed[i],DETECTOR_DIM);
        init_array(old_gram[i],DETECTOR_DEPTHS);init_array(new_gram[i],DETECTOR_DEPTHS);init_array(loss[i],DETECTOR_DEPTHS);
    }
    init_array(old_response,DETECTOR_DEPTHS);init_array(new_response,DETECTOR_DEPTHS);init_array(drift,DETECTOR_DEPTHS);
    init_array(p,DETECTOR_DIM);init_array(q,DETECTOR_DIM);init_array(lifted,DETECTOR_DIM);init_array(coupling,DETECTOR_DIM);
    init(&Dvalue);init(&Dnext);init(&x);init(&y);init(&zero);
    native_residual(f,N,p,&Dvalue);native_residual(f,4*N,q,&Dnext);
    unsigned H=native_shallow_horizon(f,&Dvalue),Hnext=native_shallow_horizon(f,&Dnext);
    unsigned count=0,depths[DETECTOR_DEPTHS];
    for(unsigned h=0;h<H&&N/(1u<<h)>=2&&!f->audit.failures;++h) {
        if(h+2>=Hnext)continue;
        if(!check(&f->audit,count<DETECTOR_DEPTHS,"transport depth capacity"))break;
        unsigned i=count++;depths[i]=h;
        native_conditioned_probe(f,N,h,old[i]);
        native_conditioned_probe(f,4*N,h+2,next[i]);
        native_lift(lifted,old[i],4*N,4,1,&f->audit);
        for(unsigned j=2;j<=4*N;++j)native_dot(coupling+j,f->gram[j],lifted,f->top);
        native_projection(f,4*N,coupling,removed[i]);
        for(unsigned j=2;j<=f->top;++j) {
            sub(&x,lifted+j,removed[i]+j);
            equal(&f->audit,&x,next[i]+j,"fourfold probe coefficient transport");
        }
        for(unsigned j=2;j<=N;++j) {
            native_dot(&x,f->gram[j],old[i],f->top);
            equal(&f->audit,&x,&zero,"old probe annihilates old clocks");
        }
        for(unsigned j=2;j<=4*N;++j) {
            native_dot(&x,f->gram[j],next[i],f->top);
            equal(&f->audit,&x,&zero,"new probe annihilates new coarse clocks");
        }
        native_dot(old_response+i,old[i],f->mean,f->top);
        native_dot(new_response+i,next[i],f->mean,f->top);
        /* <E_N,w> = <p_N,w>/2 - <p_(4N),U^2 w>. Keep both terms. */
        native_pair(f,&x,p,old[i]);scale(drift+i,&x,1,2);
        native_pair(f,&x,q,lifted);sub(drift+i,drift+i,&x);
        scale(&x,old_response+i,1,2);add(&x,&x,drift+i);
        equal(&f->audit,&x,new_response+i,"fourfold signed response transport");
        for(unsigned j=0;j<=i;++j) {
            native_pair(f,&old_gram[i][j],old[i],old[j]);
            native_pair(f,&new_gram[i][j],next[i],next[j]);
            native_pair(f,&loss[i][j],removed[i],removed[j]);
            sub(&y,&old_gram[i][j],&loss[i][j]);
            equal(&f->audit,&y,&new_gram[i][j],"fourfold complete Gram loss");
        }
    }
    int failed=f->audit.failures!=0;
    if(!failed) {
        if(json)fprintf(out,"{\"schema\":\"nfield.native-probe-transport.v1\",\"cutoff\":%u,\"next_cutoff\":%u,\"fine_cutoff\":%u,\"precision_bits\":%ld,\"observation_truncation\":false,\"paired_depths\":%u,\"shallow_horizon\":%u,\"next_shallow_horizon\":%u,",N,4*N,16*N,(long)calculation_precision,count,H,Hnext);
        else fprintf(out,"Fourfold probe transport\ncutoff=%u\nnext_cutoff=%u\npaired_depths=%u\n",N,4*N,count);
        native_field(out,"residual",&Dvalue,json,0);native_field(out,"next_residual",&Dnext,json,1);
        if(json) { emit_coeff(out,"optimizer",p,N);emit_coeff(out,"next_optimizer",q,4*N);fputs(",\"probes\":[",out); }
        for(unsigned i=0;i<count;++i) {
            if(json)fprintf(out,"%s{\"depth\":%u,\"next_depth\":%u,\"coarse_cutoff\":%u,",i?",":"",depths[i],depths[i]+2,N/(1u<<depths[i]));
            else fprintf(out,"depth=%u next_depth=%u coarse_cutoff=%u\n",depths[i],depths[i]+2,N/(1u<<depths[i]));
            native_field(out,"old_response",old_response+i,json,0);native_field(out,"next_response",new_response+i,json,1);native_field(out,"drift_pairing",drift+i,json,1);
            if(json) { emit_coeff(out,"old_coefficients",old[i],4*N);emit_coeff(out,"next_coefficients",next[i],16*N);emit_coeff(out,"removed_coefficients",removed[i],4*N);fputc('}',out); }
        }
        if(json)fputs("],\"gram\":[",out);
        for(unsigned i=0;i<count;++i)for(unsigned j=0;j<=i;++j) {
            if(json)fprintf(out,"%s{\"left\":%u,\"right\":%u,",i||j?",":"",i,j);
            else fprintf(out,"left=%u right=%u\n",i,j);
            native_field(out,"old",&old_gram[i][j],json,0);native_field(out,"next",&new_gram[i][j],json,1);native_field(out,"loss",&loss[i][j],json,1);
            if(json)fputc('}',out);
        }
        if(json)fprintf(out,"],\"checks\":%u,\"failures\":0}\n",f->audit.checks);
        else fputs("Complete directed native intervals. Transport retains signed drift and all Gram cross terms; it does not establish infinite recovery.\n",out);
    } else fprintf(stderr,"native probe transport: %s\n",f->audit.first_error);
    for(unsigned i=0;i<DETECTOR_DEPTHS;++i) {
        clear_array(old[i],DETECTOR_DIM);clear_array(next[i],DETECTOR_DIM);clear_array(removed[i],DETECTOR_DIM);
        clear_array(old_gram[i],DETECTOR_DEPTHS);clear_array(new_gram[i],DETECTOR_DEPTHS);clear_array(loss[i],DETECTOR_DEPTHS);
    }
    clear_array(old_response,DETECTOR_DEPTHS);clear_array(new_response,DETECTOR_DEPTHS);clear_array(drift,DETECTOR_DEPTHS);
    clear_array(p,DETECTOR_DIM);clear_array(q,DETECTOR_DIM);clear_array(lifted,DETECTOR_DIM);clear_array(coupling,DETECTOR_DIM);
    clear(&Dvalue);clear(&Dnext);clear(&x);clear(&y);clear(&zero);
    native_frame_clear(f);free(f);mpfr_free_cache2(MPFR_FREE_LOCAL_CACHE);calculation_precision=saved_precision;return failed;
}
