#include "gp/provider.h"
#include <stdlib.h>
#include <string.h>

static provider_string_t S(const char *s) { provider_string_t r; provider_string_dup(&r, s); return r; }
static void two(provider_list_string_t *l, const char *a, const char *b) {
    l->len = 2; l->ptr = malloc(2 * sizeof(provider_string_t)); l->ptr[0] = S(a); l->ptr[1] = S(b);
}

void exports_demo_sh_s_a_list(provider_list_string_t *ret) { two(ret, "red", "big"); }
void exports_demo_sh_s_b_rec(exports_demo_sh_s_wrap_t *ret) { two(&ret->tags, "rec", "ord"); }
bool exports_demo_sh_s_c_opt_list(provider_list_string_t *ret) { two(ret, "opt", "lst"); return true; }
bool exports_demo_sh_s_d_opt_item(exports_demo_sh_s_item_t *ret) {
    ret->name = S("apple"); ret->qty = 3; two(&ret->tags, "itm", "tag"); return true;
}
bool exports_demo_sh_s_e_opt_str(provider_string_t *ret) { *ret = S("solo"); return true; }
bool exports_demo_sh_s_f_res_list(provider_list_string_t *ret, provider_string_t *err) { (void)err; two(ret, "res", "ok"); return true; }
bool exports_demo_sh_s_g_opt_wrap(exports_demo_sh_s_wrap_t *ret) { two(&ret->tags, "owr", "apx"); return true; }
void exports_demo_sh_s_h_list_opt_str(provider_list_option_string_t *ret) {
    ret->len = 2; ret->ptr = malloc(2 * sizeof(provider_option_string_t));
    ret->ptr[0].is_some = true; ret->ptr[0].val = S("los");
    ret->ptr[1].is_some = true; ret->ptr[1].val = S("two");
}
void exports_demo_sh_s_p_opt_list(provider_list_string_t *x, provider_string_t *ret) {
    char b[64] = "none";
    if (x) { size_t o = 0; for (size_t i = 0; i < x->len && o < 60; i++) { size_t n = x->ptr[i].len; if (o + n > 60) n = 60 - o; memcpy(b + o, x->ptr[i].ptr, n); o += n; b[o++] = '|'; } b[o] = 0; provider_list_string_free(x); }
    *ret = S(b);
}
static uint32_t h(const uint8_t *p, size_t n) { uint32_t s = 7; for (size_t i = 0; i < n; i++) s = s * 31 + p[i]; return s; }
uint32_t exports_demo_sh_s_q_mix(provider_string_t *a, provider_string_t *x) { uint32_t s = h(a->ptr, a->len); if (x) s ^= h(x->ptr, x->len) * 3; return s; }
uint32_t exports_demo_sh_s_r_opt_list(provider_list_string_t *x) { uint32_t s = 1; if (x) for (size_t i = 0; i < x->len; i++) s = s * 131 + h(x->ptr[i].ptr, x->ptr[i].len); return s; }
