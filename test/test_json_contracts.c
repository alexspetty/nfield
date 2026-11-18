/* Structural JSON checks for CLI and TCP results. This test parser is
 * independent of the application's request parser and response encoder. */
#include <ctype.h>
#include <errno.h>
#include <gmp.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define LIMIT (4u * 1024u * 1024u)
typedef struct Json Json;
struct Json { char kind; char *text; Json *child, *next; size_t size; };
static unsigned checks;
static void fail(const char *message) { fprintf(stderr,"JSON contract: %s\n",message); exit(1); }
#define CHECK(x) do { ++checks; if (!(x)) fail(#x); } while (0)
static void *allocate(size_t n) { void *p=calloc(1,n); if(!p) fail("allocation"); return p; }
static void space(const char **p) { while(**p && strchr(" \t\n\r",**p)) ++*p; }
static unsigned hex4(const char **p)
{
    unsigned n=0;
    for(int i=0;i<4;i++) { unsigned char c=(unsigned char)*(*p)++; unsigned v;
        if(c>='0'&&c<='9')v=c-'0'; else if(c>='a'&&c<='f')v=c-'a'+10;
        else if(c>='A'&&c<='F')v=c-'A'+10; else fail("unicode escape");
        n=16*n+v;
    } return n;
}
static char *string(const char **p)
{
    CHECK(*(*p)++=='"');
    const char *end=*p;
    while(*end && *end!='"') { if(*end=='\\' && end[1]) ++end; ++end; }
    CHECK(*end=='"');char *out=allocate((size_t)(end-*p)+1);size_t n=0;
    while(**p && **p!='"') {
        unsigned char c=(unsigned char)*(*p)++;
        if(c<32) fail("unescaped control byte");
        if(c!='\\') { out[n++]=(char)c; continue; }
        c=(unsigned char)*(*p)++;
        if(c=='"'||c=='\\'||c=='/')out[n++]=(char)c;
        else if(c=='b')out[n++]='\b'; else if(c=='f')out[n++]='\f';
        else if(c=='n')out[n++]='\n'; else if(c=='r')out[n++]='\r'; else if(c=='t')out[n++]='\t';
        else if(c=='u') {
            if(strlen(*p)<4)fail("short unicode escape");
            unsigned u=hex4(p);
            if(u>=0xd800&&u<=0xdbff) {
                if(strncmp(*p,"\\u",2))fail("missing low surrogate");
                *p+=2;
                if(strlen(*p)<4)fail("short surrogate");
                unsigned v=hex4(p);
                if(v<0xdc00||v>0xdfff)fail("invalid low surrogate");
                u=0x10000+((u-0xd800)<<10)+(v-0xdc00);
            } else if(u>=0xdc00&&u<=0xdfff)fail("isolated surrogate");
            if(u==0)fail("embedded null in contract string");
            if(u<0x80)out[n++]=(char)u;
            else if(u<0x800) { out[n++]=(char)(0xc0|(u>>6));out[n++]=(char)(0x80|(u&63)); }
            else if(u<0x10000) { out[n++]=(char)(0xe0|(u>>12));out[n++]=(char)(0x80|((u>>6)&63));out[n++]=(char)(0x80|(u&63)); }
            else { out[n++]=(char)(0xf0|(u>>18));out[n++]=(char)(0x80|((u>>12)&63));out[n++]=(char)(0x80|((u>>6)&63));out[n++]=(char)(0x80|(u&63)); }
        } else fail("unknown string escape");
    }
    CHECK(*(*p)++=='"');out[n]=0;return out;
}
static Json *parse(const char **p, unsigned depth)
{
    CHECK(depth<64);space(p);Json *j=allocate(sizeof(*j));j->kind=**p;
    if(**p=='"') { j->text=string(p);return j; }
    if(**p=='{'||**p=='[') {
        char close=*(*p)++=='{'?'}':']';Json **tail=&j->child;space(p);
        if(**p==close) {++*p;return j;}
        for(;;) {
            if(j->kind=='{') {
                CHECK(**p=='"');Json *key=parse(p,depth+1);*tail=key;tail=&key->next;
                for(Json *k=j->child;k!=key;k=k->next->next)CHECK(strcmp(k->text,key->text)!=0);
                space(p);CHECK(*(*p)++==':');
            }
            *tail=parse(p,depth+1);tail=&(*tail)->next;++j->size;space(p);
            if(**p==close) {++*p;return j;}
            CHECK(*(*p)++==',');space(p);
        }
    }
    const char *start=*p;
    if(**p=='t' && !strncmp(*p,"true",4))*p+=4;
    else if(**p=='f' && !strncmp(*p,"false",5))*p+=5;
    else if(**p=='n' && !strncmp(*p,"null",4))*p+=4;
    else {
        j->kind='0';if(**p=='-')++*p;
        CHECK(isdigit((unsigned char)**p));
        if(**p=='0')++*p;else while(isdigit((unsigned char)**p))++*p;
        if(**p=='.') { ++*p;CHECK(isdigit((unsigned char)**p));while(isdigit((unsigned char)**p))++*p; }
        if(**p=='e'||**p=='E') { ++*p;if(**p=='+'||**p=='-')++*p;CHECK(isdigit((unsigned char)**p));while(isdigit((unsigned char)**p))++*p; }
    }
    size_t n=(size_t)(*p-start);j->text=allocate(n+1);memcpy(j->text,start,n);return j;
}
static Json *document(const char *s) {Json *j=parse(&s,0);space(&s);CHECK(!*s);return j;}
static void release(Json *j) {while(j){Json *n=j->next;release(j->child);free(j->text);free(j);j=n;}}
static Json *find(Json *j,const char *key)
{
    CHECK(j && j->kind=='{');for(Json *k=j->child;k;k=k->next->next)if(!strcmp(k->text,key))return k->next;return NULL;
}
static Json *get(Json *j,const char *key) {Json *v=find(j,key);CHECK(v);return v;}
static const char *text(Json *j) {CHECK(j&&j->kind=='"');return j->text;}
static const char *field(Json *j,const char *key) {return text(get(j,key));}
static long number(Json *j) {CHECK(j&&j->kind=='0');char *e;errno=0;long n=strtol(j->text,&e,10);CHECK(!errno&&!*e);return n;}
static long integer(Json *j,const char *key) {return number(get(j,key));}
static int boolean(Json *j) {CHECK(j&&(j->kind=='t'||j->kind=='f'));return j->kind=='t';}
static double decimal(Json *j) {CHECK(j&&(j->kind=='0'||j->kind=='"'));char *e;errno=0;double d=strtod(j->text,&e);CHECK(!errno&&!*e&&isfinite(d));return d;}
static void equal(Json *j,const char *key,const char *s) {CHECK(!strcmp(field(j,key),s));}
static void rational(mpq_t q,Json *j) {CHECK(j&&(j->kind=='"'||j->kind=='0'));CHECK(mpq_set_str(q,j->text,10)==0);CHECK(mpz_sgn(mpq_denref(q))!=0);mpq_canonicalize(q);}
static Json *row(Json *rows,const char *key,long value)
{
    CHECK(rows->kind=='[');Json *found=NULL;
    for(Json *r=rows->child;r;r=r->next)if(integer(r,key)==value){CHECK(!found);found=r;}
    CHECK(found);return found;
}
static void nonempty(Json *j,const char *key) {CHECK(*field(j,key));}
static void catalog(Json *j)
{
    equal(j,"schema","nfield.commands.v1");Json *rows=get(j,"commands");CHECK(rows->kind=='['&&rows->size==107);
    int field_seen=0,forest_seen=0,fixed_seen=0;
    for(Json *r=rows->child;r;r=r->next) {
        const char *name=field(r,"name");
        for(Json *q=rows->child;q!=r;q=q->next)CHECK(strcmp(name,field(q,"name"))!=0);
        nonempty(r,"purpose");nonempty(r,"inputs");nonempty(r,"outputs");nonempty(r,"example");
        if(!strcmp(name,"field"))field_seen=1;
        if(!strcmp(name,"reset-forest")){equal(r,"kind","utility");forest_seen=1;}
        if(!strcmp(name,"special-value-moment")){equal(r,"kind","verification");fixed_seen=1;}
        const char *a[]={"actions","verificationActions"},*d[]={"actionDetails","verificationDetails"};
        for(int i=0;i<2;i++) {
            Json *aa=get(r,a[i]),*dd=get(r,d[i]);CHECK(aa->kind=='['&&dd->kind=='['&&aa->size==dd->size);
            Json *av=aa->child;
            for(Json *dv=dd->child;dv;dv=dv->next,av=av->next) {
                CHECK(!strcmp(text(av),field(dv,"name")));
                nonempty(dv,"purpose");nonempty(dv,"syntax");nonempty(dv,"inputs");nonempty(dv,"outputs");nonempty(dv,"example");nonempty(dv,"limits");
                CHECK(get(dv,"formatOptions")->kind=='[');
            }
        }
    }
    CHECK(field_seen&&forest_seen&&fixed_seen);
}
static void contracts(Json *j)
{
    CHECK(j->size==7&&integer(j,"exit_code")==0);equal(j,"schema","nfield.checks.v1");equal(j,"scope","finite-implementation");equal(j,"family","reset-forest");equal(j,"suite","contracts");
    Json *s=get(j,"summary"),*rows=get(j,"results");
    CHECK(s->size==5&&integer(s,"cases")==13034);
    CHECK(integer(s,"checks")==75&&integer(s,"passed")==75&&integer(s,"failed")==0&&integer(s,"assertions")==501493);
    CHECK(rows->kind=='['&&rows->size==75);long assertions=0,cases=0;
    for(Json *r=rows->child;r;r=r->next) {
        CHECK(r->size==6);nonempty(r,"check_id");nonempty(r,"tested_domain");equal(r,"status","pass");CHECK(integer(r,"failures")==0);
        for(Json *q=rows->child;q!=r;q=q->next)CHECK(strcmp(field(q,"check_id"),field(r,"check_id"))!=0);
        assertions+=integer(r,"assertions");cases+=integer(r,"cases");
    }
    CHECK(assertions==501493&&cases==13034);
}
static void forest(Json *j)
{
    equal(j,"schema","nfield.reset-forest.v1");CHECK(!find(j,"status"));Json *rows=get(j,"rows");CHECK(rows->kind=='[');int count=0;const long expected[]={17,23,29};
    for(Json *r=rows->child;r;r=r->next)if(!boolean(get(r,"selected"))){CHECK(count<3);CHECK(integer(r,"denominator")==expected[count++]);}
    CHECK(count==3);
}
static void source(Json *j)
{
    Json *rows=get(j,"rows");CHECK(rows->kind=='['&&rows->size==30);long total=0;
    for(Json *r=rows->child;r;r=r->next){long a=integer(r,"forest_coefficient"),b=integer(r,"complement_coefficient");CHECK(a+b==1);total+=a;}
    CHECK(total==30);
}
static void weighted(Json *j)
{
    equal(j,"schema","nfield.reset-source.v1");Json *rows=get(j,"rows");CHECK(rows->kind=='['&&rows->size==4);
    const char *expected[]={"1","-1","3/2","0"};mpq_t a,b,c,sum,e;mpq_inits(a,b,c,sum,e,NULL);int index=0;
    for(Json *r=rows->child;r;r=r->next) {
        rational(a,get(r,"original_coefficient"));rational(b,get(r,"selected_coefficient"));rational(c,get(r,"complement_coefficient"));
        CHECK(mpq_set_str(e,expected[index++],10)==0);mpq_canonicalize(e);CHECK(mpq_equal(b,e));mpq_add(sum,b,c);CHECK(mpq_equal(a,sum));
    }
    Json *energy=get(j,"energies");const char *fields[]={"continuous","sampled","defect"};
    for(int i=0;i<3;i++) {
        rational(a,get(get(energy,"original"),fields[i]));rational(b,get(get(energy,"selected"),fields[i]));rational(c,get(get(energy,"complement"),fields[i]));rational(e,get(get(energy,"twice_mixed"),fields[i]));
        mpq_add(sum,b,c);mpq_add(sum,sum,e);CHECK(mpq_equal(a,sum));
    }
    mpq_clears(a,b,c,sum,e,NULL);
}
static void native(Json *j,const char *mode)
{
    equal(j,"status","PASS");
    if(!strcmp(mode,"trace")){CHECK(integer(j,"first")==4&&integer(j,"last")==6);CHECK(!boolean(get(j,"uniform_lower_bound_proved")));}
    else if(!strcmp(mode,"collision4")){CHECK(integer(j,"first")==4&&integer(j,"last")==8);CHECK(decimal(get(get(j,"capture_fraction"),"hi"))<.001);CHECK(decimal(get(get(j,"signed_response"),"hi"))<0);}
    else {
        Json *rows=get(j,"families"),*r25=row(rows,"modulus",25);
        CHECK(integer(r25,"finite_orbit_rank")==8);
        if(!strcmp(mode,"families8")){Json *r9=row(rows,"modulus",9);CHECK(integer(r9,"finite_orbit_rank")==2&&integer(r9,"projected_shell_rank")==2);CHECK(integer(r25,"projected_shell_rank")==4&&integer(get(j,"combined"),"projected_shell_rank")==4);}
        else if(!strcmp(mode,"families16")){CHECK(integer(j,"first")==8&&integer(j,"last")==16);CHECK(!boolean(get(j,"complete_period_audit")));CHECK(integer(r25,"projected_shell_rank")==8&&boolean(get(r25,"projected_rank_exact")));}
        else {Json *c=get(j,"combined"),*r49=row(rows,"modulus",49),*e=get(j,"extension_49");CHECK(integer(c,"finite_tower_rank")==11&&integer(c,"projected_shell_rank")==11&&integer(c,"blind_codimension")==1);CHECK(integer(r49,"finite_orbit_rank")==18&&integer(r49,"projected_shell_rank")==12);CHECK(integer(e,"rank_increment")==1&&decimal(get(get(e,"prior_blind_detection_fraction"),"lo"))>.999999);}
    }
}
static void fiber(const char *output)
{
    CHECK(strstr(output,"conductor, fiber-size and cancellation discrepancies = 0"));CHECK(strstr(output,"Run nfield verify primitive-character-cancellation"));
    char *copy=allocate(strlen(output)+1);strcpy(copy,output);int rows=0;
    for(char *line=strtok(copy,"\n");line;line=strtok(NULL,"\n")) {
        int a,b,c,d,e,f;double x,y;char extra;
        if(sscanf(line,"%d %d %d %d %d %d %lf %lf %c",&a,&b,&c,&d,&e,&f,&x,&y,&extra)==8){++rows;CHECK(a==1&&b==1&&c==5&&d==rows&&e==5&&f==16);CHECK(hypot(x,y)<2e-12);}
    }
    CHECK(rows==4);free(copy);
}
int main(int argc,char **argv)
{
    if(argc<2||argc>3){fputs("Usage: test_json_contracts MODE [--raw]\n",stderr);return 2;}
    int raw=argc==3&&!strcmp(argv[2],"--raw");if(argc==3&&!raw)return 2;
    char *buffer=allocate(LIMIT+1);size_t n=fread(buffer,1,LIMIT,stdin);CHECK(!ferror(stdin)&&!(!feof(stdin)&&n==LIMIT));buffer[n]=0;
    Json *envelope=NULL,*body=NULL;const char *output=buffer,*mode=argv[1];
    if(!raw) {
        envelope=document(buffer);output=field(envelope,"output");CHECK(!boolean(get(envelope,"truncated")));
        long status=integer(envelope,"exit_code");
        if(!strcmp(mode,"retired")){CHECK(status==2&&*output);CHECK(strstr(output,"retired")||strstr(output,"removed"));CHECK(!strstr(output,"verifications passed")&&!strstr(output,"Result  PASS")&&!strchr(output,'{'));goto done;}
        if(!strcmp(mode,"invalid")){CHECK(status!=0&&*output);goto done;}
        CHECK(status==0);
    }
    if(!strcmp(mode,"help")){CHECK(strstr(output,"--weights")&&strstr(output,"--mask"));goto done;}
    if(!strcmp(mode,"fiber")){fiber(output);goto done;}
    body=document(output);
    if(!strcmp(mode,"catalog"))catalog(body);
    else if(!strcmp(mode,"contracts"))contracts(body);
    else if(!strcmp(mode,"forest"))forest(body);
    else if(!strcmp(mode,"source"))source(body);
    else if(!strcmp(mode,"weighted"))weighted(body);
    else if(!strcmp(mode,"trace")||!strcmp(mode,"collision4")||!strcmp(mode,"families8")||!strcmp(mode,"families16")||!strcmp(mode,"tower49"))native(body,mode);
    else if(strcmp(mode,"parse"))fail("unknown mode");
done:
    release(body);release(envelope);free(buffer);printf("JSON %s: %u assertions passed.\n",mode,checks);return 0;
}
