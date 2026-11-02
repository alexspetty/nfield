/* Exact Hermitian component matrices. Entries use conjugate(left)*right,
 * so arbitrary subsequent coefficients act as z* H z. */
enum { FM_CONT, FM_GRID, FM_DEFECT, FM_POINT, FM_JUMP, FM_DERIVATIVE, FM_COUNT };
static Complex *fo_matrix_new(unsigned n)
{
    Complex *m=calloc(FM_COUNT*n*n,sizeof *m);
    if(m)for(unsigned i=0;i<FM_COUNT*n*n;++i)zi(m+i);
    return m;
}
static void fo_matrix_free(Complex *m,unsigned n)
{ for(unsigned i=0;i<FM_COUNT*n*n;++i)zc(m+i);free(m); }
static void fo_outer(Complex *m,Complex *left,Complex *right,unsigned n,const mpq_t scale)
{
    Complex product;zi(&product);
    for(unsigned i=0;i<n;++i)for(unsigned j=0;j<n;++j) {
        zm(&product,left+i,right+j,1);zq(&product,&product,scale);za(m+i*n+j,m+i*n+j,&product);
    }
    zc(&product);
}
static int fo_matrix_report(Complex *m,unsigned n,int boundary)
{
    const char *names[]={"continuous","sampled","defect","point_correction","value_jump","derivative_jump"};
    unsigned size=n*n,count=boundary?FM_COUNT:3;int ok=1;
    Complex error;zi(&error);mpq_t opposite;mpq_init(opposite);
    for(unsigned i=0;i<size;++i)zd(m+FM_DEFECT*size+i,m+FM_CONT*size+i,m+FM_GRID*size+i);
    for(unsigned channel=0;channel<count;++channel)for(unsigned i=0;i<n;++i)for(unsigned j=0;j<n;++j) {
        Complex *a=m+channel*size+i*n+j,*b=m+channel*size+j*n+i;
        mpq_neg(opposite,b->im);ok=ok&&mpq_equal(a->re,b->re)&&mpq_equal(a->im,opposite);
    }
    if(boundary)for(unsigned i=0;i<size;++i) {
        za(&error,m+FM_POINT*size+i,m+FM_JUMP*size+i);za(&error,&error,m+FM_DERIVATIVE*size+i);
        zd(&error,&error,m+FM_DEFECT*size+i);ok=ok&&!mpq_sgn(error.re)&&!mpq_sgn(error.im);
    }
    if(ok) {
        printf("matrix_size=%u\n",n);
        for(unsigned channel=0;channel<count;++channel)for(unsigned i=0;i<n;++i)for(unsigned j=0;j<n;++j) {
            Complex *v=m+channel*size+i*n+j;
            gmp_printf("matrix=%s row=%u column=%u value=%Qd:%Qd\n",names[channel],i,j,v->re,v->im);
        }
        puts("Matrix entries include the supplied component amplitudes and readings. Rows and columns start at zero; coefficients act by conjugate(z) H z.");
    }
    zc(&error);mpq_clear(opposite);return ok;
}
static void fo_component_values(Complex *values,const mpq_t x,Complex data[5][FO_FIELDS],unsigned n,int pulses)
{
    for(unsigned i=0;i<n;++i) {
        if(pulses)pulse_value(values+i,x,data[0]+i,data[1]+i,data[2]+i,data[3]+i,data[4]+i,1);
        else clock_value(values+i,x,data[0]+i,data[1]+i,data[2]+i,1);
    }
}
static int fo_grid_matrix(unsigned q,const mpq_t theta,Complex data[5][FO_FIELDS],unsigned n,int pulses,mpq_t *points,unsigned boundaries)
{
    Complex *m=fo_matrix_new(n);if(!m)return 0;unsigned size=n*n;
    Complex value[FO_FIELDS],slope[FO_FIELDS],left[FO_FIELDS],right[FO_FIELDS],delta[FO_FIELDS];
    for(unsigned i=0;i<n;++i) { zi(value+i);zi(slope+i);zi(left+i);zi(right+i);zi(delta+i); }
    mpq_t x,y,width,scale,t,b2;mpq_inits(x,y,width,scale,t,b2,NULL);
    if(!pulses)for(unsigned i=0;i<n;++i) { qs(scale,data[0][i].re,2,1);zq(slope+i,data[2]+i,scale); }
    for(unsigned b=0;b<boundaries;++b) {
        mpq_add(x,points[b],points[b+1]);qs(x,x,1,2);mpq_sub(width,points[b+1],points[b]);
        fo_component_values(value,x,data,n,pulses);fo_outer(m+FM_CONT*size,value,value,n,width);
        if(!pulses) { mpq_mul(scale,width,width);mpq_mul(scale,scale,width);qs(scale,scale,1,12);fo_outer(m+FM_CONT*size,slope,slope,n,scale); }
    }
    qi(scale,1,q);
    for(unsigned a=0;a<q;++a) {
        qi(x,a,1);mpq_add(x,x,theta);qs(x,x,1,q);fo_component_values(value,x,data,n,pulses);
        fo_outer(m+FM_GRID*size,value,value,n,scale);
    }
    for(unsigned b=0;b<boundaries;++b) {
        fo_component_values(value,points[b],data,n,pulses);
        if(pulses) {
            unsigned previous=b?b-1:boundaries-1;
            mpq_add(x,points[previous],points[previous+1]);qs(x,x,1,2);fo_component_values(left,x,data,n,1);
            mpq_add(x,points[b],points[b+1]);qs(x,x,1,2);fo_component_values(right,x,data,n,1);
        } else for(unsigned i=0;i<n;++i) {
            zs(left+i,value+i);zs(right+i,value+i);
            mpq_mul(x,points[b],data[0][i].re);mpq_add(x,x,data[1][i].re);
            if(whole(x)) { za(left+i,left+i,data[2]+i);zd(right+i,right+i,data[2]+i); }
        }
        qs(x,points[b],q,1);mpq_sub(x,x,theta);
        if(whole(x)) {
            qi(scale,1,2UL*q);fo_outer(m+FM_POINT*size,left,left,n,scale);fo_outer(m+FM_POINT*size,right,right,n,scale);
            qi(scale,-1,q);fo_outer(m+FM_POINT*size,value,value,n,scale);
        }
        saw(y,x);qs(scale,y,-1,q);fo_outer(m+FM_JUMP*size,right,right,n,scale);
        mpq_neg(scale,scale);fo_outer(m+FM_JUMP*size,left,left,n,scale);
        if(!pulses) {
            fraction(y,x);mpq_mul(b2,y,y);mpq_sub(b2,b2,y);qi(t,1,6);mpq_add(b2,b2,t);qs(scale,b2,1,2UL*q*q);
            for(unsigned i=0;i<n;++i)zd(delta+i,right+i,left+i);
            fo_outer(m+FM_DERIVATIVE*size,slope,delta,n,scale);fo_outer(m+FM_DERIVATIVE*size,delta,slope,n,scale);
        }
    }
    int ok=fo_matrix_report(m,n,1);
    for(unsigned i=0;i<n;++i) { zc(value+i);zc(slope+i);zc(left+i);zc(right+i);zc(delta+i); }
    mpq_clears(x,y,width,scale,t,b2,NULL);fo_matrix_free(m,n);return ok;
}
static int fo_harmonic_matrix(unsigned q,const mpq_t theta,const long *frequencies,Complex *amplitude,unsigned n)
{
    Complex *m=fo_matrix_new(n);if(!m)return 0;unsigned size=n*n;
    Complex product;zi(&product);mpq_t scale;mpq_init(scale);
    for(unsigned i=0;i<n;++i)for(unsigned j=0;j<n;++j) {
        zm(&product,amplitude+i,amplitude+j,1);long difference=frequencies[j]-frequencies[i];
        if(!difference)zs(m+FM_CONT*size+i*n+j,&product);
        if(difference%(long)q==0) {
            qi(scale,mpq_sgn(theta)&&((difference/(long)q)%2)?-1:1,1);
            zq(m+FM_GRID*size+i*n+j,&product,scale);
        }
    }
    int ok=fo_matrix_report(m,n,0);zc(&product);mpq_clear(scale);fo_matrix_free(m,n);return ok;
}
