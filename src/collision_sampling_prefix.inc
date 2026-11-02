/* Complete finite prefix populations and the all-residue stopped-cost
 * extension. Keep strict nearest-remainder endpoints and both orientations. */
static unsigned cs_prefix_word(unsigned A,long B,unsigned *digits,int *signs)
{
    unsigned length=0;
    while(B) {
        unsigned previous=(unsigned)labs(B),digit=A/previous;
        while(!cs_golden(previous,(long)A-(long)digit*previous)
              && !(previous==1 && A==digit)) ++digit;
        digits[length]=digit;signs[length++]=B>0?1:-1;
        B=(long)A-(long)digit*previous;A=previous;
    }
    return length;
}
static int cs_prefix_population(unsigned first,unsigned last)
{
    if(first<2 || last<first || last>512)return 1;
    unsigned total=0;
    for(unsigned A=first;A<=last;++A) {
        unsigned positive=0,negative=0;
        for(long B=-(long)A+1;B<(long)A;++B) {
            long C,E;int determinant;
            if(labs(B)<2 || !cs_prefix_row(A,B,&C,&E,&determinant))continue;
            unsigned digits[32];int signs[32];unsigned length=cs_prefix_word(A,B,digits,signs);
            printf("A=%u B=%ld C=%ld E=%ld determinant=%d length=%u word=",A,B,C,E,determinant,length);
            for(unsigned j=length;j>0;--j)printf("%s%u:%d",j==length?"":",",digits[j-1],signs[j-1]);
            putchar('\n');++total;if(determinant>0)++positive;else ++negative;
        }
        printf("denominator=%u positive_orientation=%u negative_orientation=%u population=%u\n",A,positive,negative,positive+negative);
    }
    printf("first=%u last=%u total_population=%u\n",first,last,total);
    puts("Complete primitive top rows of words of length at least two; both orientations and strict golden-interval endpoints are retained.");
    return 0;
}
static int cs_stopped_costs(unsigned k,unsigned H)
{
    if(k<2 || k>512 || H<1 || H>k)return 1;
    mpq_t cost[512],term,jump,variation,bound,margin;
    for(unsigned c=0;c<k;++c)mpq_init(cost[c]);
    mpq_inits(term,jump,variation,bound,margin,NULL);
    /* Every real ratio in a prefix's open support has the same unique
     * nearest-remainder path. Thus this evaluates the prefix-interval sum
     * on nonunits too. Outside 0<c<k/2 its zero extension is retained. */
    for(unsigned c=1;2*c<k;++c) {
        unsigned a=k,b=c;int determinant=1;
        for(;;) {
            int orientation;unsigned digit,e=cs_nearest(a,b,&orientation,&digit);
            if(!e || 2*e==b || e<=H)break;
            determinant=-orientation*determinant;
            cs_reciprocity(term,e,b);cs_scale(term,term,-determinant,1);
            mpq_add(cost[c],cost[c],term);a=b;b=e;
        }
    }
    for(unsigned c=0;c<k;++c) {
        mpq_sub(jump,cost[c],cost[(c+k-1)%k]);mpq_abs(term,jump);mpq_add(variation,variation,term);
    }
    cs_fraction(bound,8L*k*k,(unsigned long)H*H);mpq_sub(margin,bound,variation);
    int failed=mpq_sgn(margin)<0 || mpq_sgn(cost[0]);
    if(!failed) {
        printf("modulus=%u threshold=%u\n",k,H);
        for(unsigned c=0;c<k;++c) {
            mpq_sub(jump,cost[c],cost[(c+k-1)%k]);
            gmp_printf("residue=%u unit=%u cost=%Qd cyclic_jump=%Qd\n",c,cs_gcd(c,k)==1,cost[c],jump);
        }
        cs_print("cyclic_variation",variation);cs_print("variation_bound",bound);cs_print("variation_margin",margin);
        puts("Zero outside the strict half interval; nonunit residues and both endpoint jumps are included. The bound is checked at this modulus and threshold.");
    }
    for(unsigned c=0;c<k;++c)mpq_clear(cost[c]);
    mpq_clears(term,jump,variation,bound,margin,NULL);return failed;
}
