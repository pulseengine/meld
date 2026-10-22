#include "gp/provider.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

struct exports_demo_cx_store_counter_t { uint32_t value; };
static exports_demo_cx_store_item_t items[8];
static uint32_t nitems;

static void dup_str(provider_string_t *d, const provider_string_t *s) { provider_string_dup_n(d, (const char *)s->ptr, s->len); }

exports_demo_cx_store_own_counter_t exports_demo_cx_store_constructor_counter(uint32_t start) {
    exports_demo_cx_store_counter_t *r = malloc(sizeof *r); r->value = start;
    return exports_demo_cx_store_counter_new(r);
}
uint32_t exports_demo_cx_store_method_counter_bump(exports_demo_cx_store_borrow_counter_t self, uint32_t by) { return self->value += by; }
void exports_demo_cx_store_method_counter_label(exports_demo_cx_store_borrow_counter_t self, provider_string_t *ret) {
    char b[32]; snprintf(b, sizeof b, "counter=%u", self->value); provider_string_dup(ret, b);
}
void exports_demo_cx_store_counter_destructor(exports_demo_cx_store_counter_t *rep) { free(rep); }
bool exports_demo_cx_store_put(exports_demo_cx_store_item_t *it, uint32_t *ret, provider_string_t *err) {
    if (it->qty == 0 || nitems == 8) { provider_string_dup(err, it->qty == 0 ? "qty must be > 0" : "full"); exports_demo_cx_store_item_free(it); return false; }
    items[nitems] = *it;            /* takes ownership */
    *ret = nitems++;
    return true;
}
bool exports_demo_cx_store_get(uint32_t id, exports_demo_cx_store_item_t *ret) {
    if (id >= nitems) return false;
    exports_demo_cx_store_item_t *s = &items[id];
    dup_str(&ret->name, &s->name); ret->qty = s->qty;
    ret->tags.len = s->tags.len; ret->tags.ptr = malloc(sizeof(provider_string_t) * (s->tags.len ? s->tags.len : 1));
    for (size_t i = 0; i < s->tags.len; i++) dup_str(&ret->tags.ptr[i], &s->tags.ptr[i]);
    return true;
}
uint64_t exports_demo_cx_store_area(exports_demo_cx_store_shape_t *s) {
    switch (s->tag) {
    case EXPORTS_DEMO_CX_STORE_SHAPE_CIRCLE: return 3ull * s->val.circle * s->val.circle;
    case EXPORTS_DEMO_CX_STORE_SHAPE_RECT: return (uint64_t)s->val.rect.f0 * s->val.rect.f1;
    default: return 0;
    }
}
exports_demo_cx_store_level_t exports_demo_cx_store_classify(uint32_t n) { return n < 10 ? 0 : n < 100 ? 1 : 2; }
exports_demo_cx_store_perms_t exports_demo_cx_store_check(exports_demo_cx_store_perms_t p) { return p & ~EXPORTS_DEMO_CX_STORE_PERMS_EXEC; }
uint64_t exports_demo_cx_store_sum(provider_list_u32_t *xs) { uint64_t s = 0; for (size_t i = 0; i < xs->len; i++) s += xs->ptr[i]; provider_list_u32_free(xs); return s; }
exports_demo_cx_store_own_counter_t exports_demo_cx_store_make(uint32_t start) { return exports_demo_cx_store_constructor_counter(start); }
uint32_t exports_demo_cx_store_peek(exports_demo_cx_store_borrow_counter_t c) { return c->value; }
