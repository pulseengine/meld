#include "gg/guest.h"
#include <stdio.h>
#include <string.h>

#define L2(l) (int)(l).ptr[0].len, (l).ptr[0].ptr, (int)(l).ptr[1].len, (l).ptr[1].ptr

void exports_demo_sh_app_run_all(guest_string_t *ret) {
    char out[1024]; int o = 0;
    guest_list_string_t l; demo_sh_s_wrap_t w; demo_sh_s_item_t it; guest_string_t s, e;
    demo_sh_s_a_list(&l);
    o += snprintf(out + o, sizeof out - o, "a=%zu[%.*s,%.*s];", l.len, L2(l));
    demo_sh_s_b_rec(&w);
    o += snprintf(out + o, sizeof out - o, "b=%zu[%.*s,%.*s];", w.tags.len, L2(w.tags));
    if (demo_sh_s_c_opt_list(&l)) o += snprintf(out + o, sizeof out - o, "c=%zu[%.*s,%.*s];", l.len, L2(l));
    if (demo_sh_s_d_opt_item(&it)) o += snprintf(out + o, sizeof out - o, "d=%.*s,%u,%zu[%.*s,%.*s];", (int)it.name.len, it.name.ptr, it.qty, it.tags.len, L2(it.tags));
    if (demo_sh_s_e_opt_str(&s)) o += snprintf(out + o, sizeof out - o, "e=%.*s;", (int)s.len, s.ptr);
    if (demo_sh_s_f_res_list(&l, &e)) o += snprintf(out + o, sizeof out - o, "f=%zu[%.*s,%.*s];", l.len, L2(l));
    if (demo_sh_s_g_opt_wrap(&w)) o += snprintf(out + o, sizeof out - o, "g=%zu[%.*s,%.*s];", w.tags.len, L2(w.tags));
    guest_list_option_string_t lo; demo_sh_s_h_list_opt_str(&lo);
    o += snprintf(out + o, sizeof out - o, "h=%zu[%.*s,%.*s];", lo.len, (int)lo.ptr[0].val.len, lo.ptr[0].val.ptr, (int)lo.ptr[1].val.len, lo.ptr[1].val.ptr);
    guest_string_t t[2]; guest_string_set(&t[0], "arg"); guest_string_set(&t[1], "in");
    guest_list_string_t al = {t, 2};
    demo_sh_s_p_opt_list(&al, &s);
    o += snprintf(out + o, sizeof out - o, "p=%.*s", (int)s.len, s.ptr);
    guest_string_t qa, qx; guest_string_set(&qa, "left"); guest_string_set(&qx, "right");
    o += snprintf(out + o, sizeof out - o, ";q=%u", demo_sh_s_q_mix(&qa, &qx));
    o += snprintf(out + o, sizeof out - o, ";r=%u", demo_sh_s_r_opt_list(&al));
    guest_string_dup(ret, out);
}
