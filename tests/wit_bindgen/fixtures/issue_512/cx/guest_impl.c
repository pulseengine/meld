#include "gg/guest.h"
#include <stdio.h>
#include <string.h>

static guest_string_t S(const char *s) { guest_string_t r; guest_string_set(&r, s); return r; }

void exports_demo_cx_app_run_all(guest_string_t *ret) {
    char out[1024]; int o = 0;
    guest_string_t tags[2] = {S("red"), S("big")};
    demo_cx_store_item_t it = {S("apple"), 3, {tags, 2}};
    uint32_t id; guest_string_t err;
    bool ok = demo_cx_store_put(&it, &id, &err);
    o += snprintf(out + o, sizeof out - o, "put=%s%u;", ok ? "ok:" : "err", ok ? id : 0);
    demo_cx_store_item_t bad = {S("zero"), 0, {NULL, 0}};
    ok = demo_cx_store_put(&bad, &id, &err);
    if (!ok) { o += snprintf(out + o, sizeof out - o, "put0=err:%.*s;", (int)err.len, err.ptr); guest_string_free(&err); }
    demo_cx_store_item_t got;
    if (demo_cx_store_get(0, &got)) {
        o += snprintf(out + o, sizeof out - o, "get=%.*s,%u,[%.*s,%.*s];", (int)got.name.len, got.name.ptr, got.qty,
                      (int)got.tags.ptr[0].len, got.tags.ptr[0].ptr, (int)got.tags.ptr[1].len, got.tags.ptr[1].ptr);
        demo_cx_store_item_free(&got);
    }
    o += snprintf(out + o, sizeof out - o, "get9=%s;", demo_cx_store_get(9, &got) ? "some" : "none");
    demo_cx_store_shape_t c = {.tag = 0, .val.circle = 4}, r = {.tag = 1, .val.rect = {6, 7}}, n = {.tag = 2};
    o += snprintf(out + o, sizeof out - o, "area=%llu,%llu,%llu;", (unsigned long long)demo_cx_store_area(&c),
                  (unsigned long long)demo_cx_store_area(&r), (unsigned long long)demo_cx_store_area(&n));
    o += snprintf(out + o, sizeof out - o, "level=%u,%u,%u;", demo_cx_store_classify(5), demo_cx_store_classify(50), demo_cx_store_classify(500));
    o += snprintf(out + o, sizeof out - o, "perms=%u;", demo_cx_store_check(7));
    uint32_t xs[] = {1, 2, 3, 4000000000u}; guest_list_u32_t l = {xs, 4};
    o += snprintf(out + o, sizeof out - o, "sum=%llu;", (unsigned long long)demo_cx_store_sum(&l));
    demo_cx_store_own_counter_t k = demo_cx_store_constructor_counter(10);
    demo_cx_store_borrow_counter_t kb = demo_cx_store_borrow_counter(k);
    uint32_t b1 = demo_cx_store_method_counter_bump(kb, 5);
    guest_string_t lab; demo_cx_store_method_counter_label(kb, &lab);
    demo_cx_store_own_counter_t m = demo_cx_store_make(100);
    uint32_t pk = demo_cx_store_peek(demo_cx_store_borrow_counter(m));
    o += snprintf(out + o, sizeof out - o, "counter=%u,%.*s,peek=%u", b1, (int)lab.len, lab.ptr, pk);
    guest_string_free(&lab);
    demo_cx_store_counter_drop_own(k); demo_cx_store_counter_drop_own(m);
    guest_string_dup(ret, out);
}
