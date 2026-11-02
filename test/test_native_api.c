#include "../src/native_arithmetic.h"
#include "../src/native_refinement.h"
#include <assert.h>
#include <stdio.h>
int main(void) {
    mpq_t out[33];for(unsigned i=0;i<33;++i) { mpq_init(out[i]);mpq_set_ui(out[i],17,3); }
    assert(!native_packet_coefficients(NULL,33,2));
    assert(!native_packet_coefficients(out,16,2));
    assert(!native_packet_coefficients(out,33,1));
    assert(!native_packet_coefficients(out,33,129));
    for(unsigned i=0;i<33;++i)assert(mpq_cmp_ui(out[i],17,3)==0);
    assert(native_packet_coefficients(out,33,2));
    assert(mpq_cmp_ui(out[32],17,3)==0);
    for(unsigned i=0;i<33;++i)mpq_clear(out[i]);
    puts("PASS native packet API: invalid input preserves initialized output; valid output preserves entries beyond its documented extent.");
    FILE *before=tmpfile(),*after=tmpfile(),*probe=tmpfile();
    assert(before&&after&&probe);
    assert(native_refinement_probe_transport(2,NULL,1));
    assert(native_refinement_probe_transport(1,probe,1));
    assert(native_refinement_probe_transport(9,probe,1));
    assert(ftell(probe)==0);
    assert(!native_refinement_detector(2,before,1));
    assert(!native_refinement_probe_transport(2,probe,1));
    assert(ftell(probe)>0);
    assert(!native_refinement_detector(2,after,1));
    rewind(before);rewind(after);
    int a,b;do { a=fgetc(before);b=fgetc(after);assert(a==b); } while(a!=EOF);
    assert(!ferror(before)&&!ferror(after));
    fclose(before);fclose(after);fclose(probe);
    puts("PASS native probe transport API: rejected calls preserve output and successful calls restore caller precision.");
    return 0;
}
