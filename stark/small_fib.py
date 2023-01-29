import poly
import fri
from poly import PrimeField
from fri import gen_fri_object_with_params, Fri
import random
import sys

def get_root_of_unity(p, g, dlen):
    pf = PrimeField(p)
    root_of_unity = pow(g, (p-1)//dlen, p)
    return root_of_unity

def get_degree(p):
    return len(p) - 1

def get_domains(p, w, dlen):
    return [pow(w, i, p) for i in range(dlen)]

def trim_poly(p):
    rp = p.copy()
    rp.reverse()
    for c in rp:
        if c == 0:
            del p[-1]
        else:
            break
    return p

def adj_poly(adj_degree):
    p = []
    for i in range(adj_degree):
        p.append(0)
    p.append(1)
    return p

def verify_root_of_unity(p, dlen, root_of_unity):
    llist = [1]
    for i in range(1, dlen*2):
        v = pow(root_of_unity, i, p)
        if v == 1:
            break
        else:
            llist.append(v)
    assert dlen == len(llist)

def test_large_p():
    # NOTE FOR LARGE_P:
    # -- maximum divisor for this (large_p - 1) is 2^40
    # -- which means we can easily pick out a domain length from 2^1 ~ 2^40
    # -- w=7 is a generator for this large_p
    large_p = (2**128) - (45 * 2**40) + (1)
    max_divisor = 2**40
    g = 7
    d_trace_len = 2**4  # 16
    d_lde_len = 2**4 * 4 # 64
    # [TODO] how to figure out d_ev_len and w_ev from constraints?

    w_trace = get_root_of_unity(large_p, g, d_trace_len)
    w_lde = get_root_of_unity(large_p, g, d_lde_len)

    verify_root_of_unity(large_p, d_trace_len, w_trace)
    verify_root_of_unity(large_p, d_lde_len, w_lde)

def test_small_p():
    p = 257
    max_divisor = 256
    g = 3
    blowup = 16
    d_trace_len = 4
    d_lde_len = d_trace_len * blowup

    # [TODO] how to figure out d_ev_len and w_ev from constraints?
    max_constraint_degree = 8
    d_ev_len = d_trace_len * d_trace_len
    
    w_trace = get_root_of_unity(p, g, d_trace_len)
    w_lde = get_root_of_unity(p, g, d_lde_len)
    w_ev = get_root_of_unity(p, g, d_ev_len)

    verify_root_of_unity(p, d_trace_len, w_trace)
    verify_root_of_unity(p, d_lde_len, w_lde)
    verify_root_of_unity(p, d_ev_len, w_ev)
    #d_trace = [pow(g, i, p) for i in range(max_divisor)]
    #d_lde = [pow(w_lde, i, p) for i in range(d_lde_len)]
    #d_ev = [pow(w_ev, i, p) for i in range(d_ev_len)]

def fibo_rule(pf, a, b, c):
    return pf.sub(pf.add(a, b), c)

def prove_small_fib_transition_constraint(p, g, blowup, trace):
    # domain set-up
    pf = PrimeField(p)
    n = p - 1
    d_trace_len = len(trace)  # 8
    d_lde_len = d_trace_len * blowup  # 128
    max_constraint_degree = 8
    d_ev_len = d_trace_len * max_constraint_degree

    w_trace = get_root_of_unity(p, g, d_trace_len)
    w_lde = get_root_of_unity(p, g, d_lde_len)
    w_ev = get_root_of_unity(p, g, d_ev_len)

    d_trace = get_domains(p, w_trace, d_trace_len)
    d_lde = get_domains(p, w_lde, d_lde_len)
    d_ev = get_domains(p, w_ev, d_ev_len)

    # NOTE for constraints
    # input constraint: (1) t[0]=1 --> t[0]-1=0,  (2) t[1]=2 --> t[1]-2=0
    # output constraint: t[7]=34 --> t[7]-34=0
    # transition constraint: t[i]+t[i+1]=t[i+2] --> t[i]+t[i+1]-t[i+2]=0

    # 1. build a trace polynomial, T(x), deg(T) = 3
    tx = pf.lagrange_interp(d_trace, trace)
    
    # 2. lde trace
    trace_lde = [pf.eval_poly_at(tx, x) for x in d_lde]

    # 3. transition constraint (no adjustment degree now)
    # P(x) = T(x) + T(x*w_trace) - T(x*w_trace^2) (= 0)
    # D(x) = (x-w_trace^0)(x-w_trace^1)...(x-w_trace^5) --> denominator
    # P(x) = C(x) * D(x)
    # C(x) = P(x) / D(x) --> domain: evaluation domain except ones that evaluate D(x) to 0.
    input_list = []
    for i in range(0, len(trace_lde) - 2*blowup, 2):
        input_list.append((trace_lde[i], trace_lde[i+blowup], trace_lde[i+blowup*2]))
    px_ev = [pf.sub(pf.add(x[0], x[1]), x[2]) for x in input_list]
    px = trim_poly(pf.lagrange_interp(d_ev[:len(px_ev)], px_ev))

    # 4. compute dx
    dx = [1]
    for i in range(d_trace_len - 2):
        dx = pf.mul_polys(dx, [-d_trace[i], 1])

    # 5. return trace polynomial, transition constraint polynomial, and denominator
    return (tx, px, dx)

def verify_small_fib_transition_constraint(p, g, blowup, tx, px, dx):
    # domain set-up
    pf = PrimeField(p)
    n = p - 1
    d_trace_len = len(tx)  # 8
    d_lde_len = d_trace_len * blowup  # 128
    max_constraint_degree = 8
    d_ev_len = d_trace_len * max_constraint_degree

    w_trace = get_root_of_unity(p, g, d_trace_len)
    w_lde = get_root_of_unity(p, g, d_lde_len)
    w_ev = get_root_of_unity(p, g, d_ev_len)

    d_trace = get_domains(p, w_trace, d_trace_len)
    d_lde = get_domains(p, w_lde, d_lde_len)
    d_ev = get_domains(p, w_ev, d_ev_len)

    # 1. check consistency between tx and px is correct using out-of-domain point
    # T(ood_x) + T(ood_x*w_trace) - T(ood_x*w_trace^2) = P(ood_x)
    # [TODO] ood_x should be randomly chosen or set by fiat-shamir transform
    ood_x = 254  # out-of-domain x
    left = pf.sub(pf.add(pf.eval_poly_at(tx, ood_x), pf.eval_poly_at(tx, pf.mul(ood_x, w_trace))), pf.eval_poly_at(tx, pf.mul(ood_x, pf.exp(w_trace, 2))))
    right = pf.eval_poly_at(px, ood_x)
    assert left == right

    # NOTE: there are two ways to check constraints are held correctly-
    # (1) checking if P(x) is zero at all trace indexes --> the most straightforward way, but not efficient, and not probabilistically secure
    # (2) the bound degree check using FRI --> pick this one!
    
    # (1) checking if P(x) is zero at all trace indexes
    for i in range(d_trace_len - 2):
        if pf.eval_poly_at(px, d_trace[i]) != 0:
            print("[verification fail] evaluation check error!")
    
    # (2) the bound degree check using FRI
    # P(x) = T(x) + T(x*w_trace) - T(x*w_trace^2) --> deg(T)=7 such that deg(P)=7
    # D(x) = (x-w_trace^0)(x-w_trace^1)...(x-w_trace^5) --> deg(D) = 6
    # C(x) = P(x) / D(x) --> deg(C) = deg(T) - deg(D) = 1
    # target_bound_degree = 1 --> deg(C) must be equal to or less than 1 if all constraints are held properly.
    target_bound_degree = len(px) - len(dx)
    cx_ev = []
    d_cx = []
    for x in d_ev:
        denom = pf.eval_poly_at(dx, x)
        if denom != 0:
            cx_ev.append(pf.div(pf.eval_poly_at(px, x), denom))
            d_cx.append(x)
    
    # do the check directly instead of invoking FRI [TODO] call FRI to verify it
    cx = trim_poly(pf.lagrange_interp(d_cx, cx_ev))
    if get_degree(cx) > target_bound_degree:
        print("[verification fail] the bounded degree check fail")
    
    # FRI verification (just simulating FRI)
    # [TODO] get the interface of FRI protocol correctly done-!
    # -- [TODO] fri.prove() invoked by prover, fri.verify() invoked by verifier
    # -- [TODO] fri computation without the need of feeding fx.
    fri = gen_fri_object_with_params(p, cx, w_ev, d_ev)
    fri.prove()
    fri.verify()
    # -- end

def prove_small_fib_constraint_all(p, g, blowup, trace):
    # domain set-up
    pf = PrimeField(p)
    n = p - 1
    d_trace_len = len(trace)  # 8
    d_lde_len = d_trace_len * blowup  # 128
    max_constraint_degree = 8
    d_ev_len = d_trace_len * max_constraint_degree

    w_trace = get_root_of_unity(p, g, d_trace_len)
    w_lde = get_root_of_unity(p, g, d_lde_len)
    w_ev = get_root_of_unity(p, g, d_ev_len)

    d_trace = get_domains(p, w_trace, d_trace_len)
    d_lde = get_domains(p, w_lde, d_lde_len)
    d_ev = get_domains(p, w_ev, d_ev_len)

    # NOTE for constraints
    # input constraint: (1) t[0]=1 --> t[0]-1=0,  (2) t[1]=2 --> t[1]-2=0
    # output constraint: t[7]=34 --> t[7]-34=0
    # transition constraint: t[i]+t[i+1]=t[i+2] --> t[i]+t[i+1]-t[i+2]=0

    # 1. build a trace polynomial, T(x), deg(T) = 3
    tx = pf.lagrange_interp(d_trace, trace)
    
    # 2. lde trace
    trace_lde = [pf.eval_poly_at(tx, x) for x in d_lde]

    # 3. set target degree
    boundary_target_degree = d_ev_len - (d_trace_len - 1)
    transition_target_degree = d_ev_len - 2
    constraint_target_degree = d_ev_len - d_trace_len  # after denominators divided out
    composition_target_degree = constraint_target_degree - 1

    # [TODO] 20230129: replace polynomial operations with direct value operations

    # 4. input boundary constraint
    # input_boundary_px (IBP(x)):
    # -- for constraint t[0]-1=0 (intput constraint)
    # -- IBP(x) = T(x)-1,  IBP(x) = IBC(x) * (x-1),  IBC(x) = IBP(x) / (x-1)
    stride = (int)(blowup / max_constraint_degree)
    #trace_lde[0] = 2  # --> violating the input constraint. trace_lde[0] == trace[0], this attack holds trace as it but corrupts trace_lde!
    ibp_ev = [pf.sub(x, 1) for x in trace_lde[::2]]
    boundary_adj_degree = boundary_target_degree - get_degree(tx)  # deg(ibp) must be equal to less than 7.
    boundary_adj = adj_poly(boundary_adj_degree)
    ibp_ev = [pf.add(y, pf.mul(y, pf.eval_poly_at(boundary_adj, x))) for x, y in zip(d_ev, ibp_ev)]
    ibp_dx = [-1, 1]  # denominator
    ibp_ev_divided = [pf.div(y, pf.eval_poly_at(ibp_dx, x)) for x, y in zip(d_ev[1:], ibp_ev[1:])]
    ibp_divided = trim_poly(pf.lagrange_interp(d_ev[1:], ibp_ev_divided))
    #print(get_degree(ibp_divided) <= constraint_target_degree)  # test bound degree check on ibp

    # 5. output boundary constraint
    # output_boundary_px (OBP(x)): for constraint t[7]-34=0 (output constraint)
    #trace_lde[112] = 37  # --> violating the output constraint. trace[7] == trace_lde[7 * blowup(16)] (7*16=112) (d_ev[7*8])
    obp_ev = [pf.sub(x, 34) for x in trace_lde[::2]]
    obp_ev = [pf.add(y, pf.mul(y, pf.eval_poly_at(boundary_adj, x))) for x, y in zip(d_ev, obp_ev)]
    obp_dx = [-d_trace[7], 1]  # denominator
    obp_ev_divided_domain = []
    obp_ev_divided = []
    for i in range(d_ev_len):
        if i != 7 * 8:
            obp_ev_divided_domain.append(d_ev[i])
            obp_ev_divided.append(pf.div(obp_ev[i], pf.eval_poly_at(obp_dx, d_ev[i])))
    obp_divided = trim_poly(pf.lagrange_interp(obp_ev_divided_domain, obp_ev_divided))
    #print(get_degree(obp_divided) <= constraint_target_degree) # test bound degree check on obp

    # 6. transition constraint (TP(x))
    # P(x) = T(x) + T(x*w_trace) - T(x*w_trace^2) (= 0)
    # D(x) = (x-w_trace^0)(x-w_trace^1)...(x-w_trace^5) --> denominator
    # P(x) = C(x) * D(x)
    # C(x) = P(x) / D(x) --> domain: evaluation domain except ones that evaluate D(x) to 0.
    input_list = []
    for i in range(0, len(trace_lde) - 2*blowup, 2):
        input_list.append((trace_lde[i], trace_lde[i+blowup], trace_lde[i+blowup*2]))
    tp_ev = [pf.sub(pf.add(x[0], x[1]), x[2]) for x in input_list]
    tp = trim_poly(pf.lagrange_interp(d_ev[:len(tp_ev)], tp_ev))
    transition_adj_degree = transition_target_degree - get_degree(tx) # deg(tp) must be equal to less than 7.
    tp_adj = pf.mul_polys(tp, adj_poly(transition_adj_degree))
    tp = pf.add_polys(tp, tp_adj)
    tp_dx = [1]  # denominator
    for i in range(d_trace_len - 2):
        tp_dx = pf.mul_polys(tp_dx, [-d_trace[i], 1])
    tp_ev_divided_domain = []
    tp_ev_divided = []
    for i in range(d_ev_len):
        skip = False
        for x in d_trace[:d_trace_len-2]:
            if d_ev[i] == x:
                skip = True
                break
        if skip == False:
            tp_ev_divided_domain.append(d_ev[i])
            tp_ev_divided.append(pf.div(pf.eval_poly_at(tp, d_ev[i]), pf.eval_poly_at(tp_dx, d_ev[i])))
    tp_divided = trim_poly(pf.lagrange_interp(tp_ev_divided_domain, tp_ev_divided))
    #print(get_degree(tp_divided) <= constraint_target_degree)  # test bound degree check on obp

    # 8. mix boundary constraint and transition constraint into a single constraint polynomial (CP(x))
    # [TODO] random coefficients for a linear combination
    cx = pf.add_polys(ibp_divided, obp_divided)
    cx = pf.add_polys(cx, tp_divided)
    #print(get_degree(cx) <= constraint_target_degree)  # test bound degree check on cx
    
    # [TEST] consistency check on composition polynomial? --> interesting point--! (blog post)
    # Intuition: have the bounded degree check be also in charge of ood_x values
    # Previous argument (without composition poly, only considering one constraint poly)
    # ---- check a relationship between tx and cx directly-:)
    # [Q] Current argument for composition poly (simple consistency check is not viable to perform)
    # ---- checking tx-cx relationship, how? --> leading to a different constraint_evaluation_at_ood_x
    #     -- check on distaff
    #     -- evaluation at z is different
    #     -- doing something on tx-cx at ood_x
    #     -- t[ood_x] --> boundary_chec
    #
    # [ALGO]
    #    (1) t[254], t[255], t[256] --> authentic
    #    (2) C(x) = IBP(x) + OBP(x) + TP(x)
    #    (2) for input constraint: IBP(x) = T(x) - 1 --> (t(254)-1) / (254 - w_trace_0(1)) --> v1
    #    (3) for output constraint: OBP(x) = T(x) - 34 --> (t(254)-34) / (254 - w_trace_7(?)) --> v2
    #    (4) for transition constraint: TP(x) = ... --> (t[254]+t[255]-t[256]) / (denom...) --> v3
    #    (5) C(254) = v1+v2+v3  --> value the verifier will build from trace
    #    --> consistency check is still possible, even on a combined constraint poly--!

    # 9. build a composition polynomial at ood_x (replace consistency check with the bound degree check)
    # [TODO] random coefficients
    ood_x = 254
    ood_x2 = pf.mul(ood_x, w_trace)
    ood_x3 = pf.mul(ood_x2, w_trace)
    composition_adj_degree = constraint_target_degree - get_degree(tx)
    composition_adj = adj_poly(composition_adj_degree)

    ood_x_val = pf.eval_poly_at(tx, ood_x)
    ood_x2_val = pf.eval_poly_at(tx, ood_x2)
    ood_x3_val = pf.eval_poly_at(tx, ood_x3)
    ood_x_cval = pf.eval_poly_at(cx, ood_x)

    cp_t1_ev = [pf.sub(pf.eval_poly_at(tx, x), ood_x_val) for x in d_lde]
    cp_t1_ev = [pf.div(y, pf.sub(x, ood_x)) for x, y in zip(d_lde, cp_t1_ev)]

    cp_t2_ev = [pf.sub(pf.eval_poly_at(tx, x), ood_x2_val) for x in d_lde]
    cp_t2_ev = [pf.div(y, pf.sub(x, ood_x2)) for x, y in zip(d_lde, cp_t2_ev)]

    cp_t3_ev = [pf.sub(pf.eval_poly_at(tx, x), ood_x3_val) for x in d_lde]
    cp_t3_ev = [pf.div(y, pf.sub(x, ood_x3)) for x, y in zip(d_lde, cp_t3_ev)]

    cp_t_ev = [pf.add(pf.add(x, y), z) for x, y, z in zip(cp_t1_ev, cp_t2_ev, cp_t3_ev)]
    cp_t_ev = [pf.add(y, pf.mul(y, pf.eval_poly_at(composition_adj, x))) for x, y in zip(d_lde, cp_t_ev)]

    cp_c_ev = [pf.sub(pf.eval_poly_at(cx, x), ood_x_cval) for x in d_lde]
    cp_c_ev = [pf.div(y, pf.sub(x, ood_x)) for x, y in zip(d_lde, cp_c_ev)]

    # 10. evaluate the composition polynomial (CP(x)) over d_lde
    cp_ev = [pf.add(x, y) for x, y in zip(cp_t_ev, cp_c_ev)] # rebuilt from everyting, this is what needs to be passed on to FRI.
    cp = trim_poly(pf.lagrange_interp(d_lde, cp_ev))

    # 11. return: verifier needs data to put together cp_ev.
    # [TODO] a small fraction of trace and constraint evaluation points, instead of the whole points
    return (tx, cx, ood_x, cp_ev)

def verify_small_fib_constraint_all(p, g, blowup, tx, cx, ood_x, cp_ev):
    # domain set-up
    pf = PrimeField(p)
    n = p - 1
    d_trace_len = len(trace)  # 8
    d_lde_len = d_trace_len * blowup  # 128
    max_constraint_degree = 8
    d_ev_len = d_trace_len * max_constraint_degree

    w_trace = get_root_of_unity(p, g, d_trace_len)
    w_lde = get_root_of_unity(p, g, d_lde_len)
    w_ev = get_root_of_unity(p, g, d_ev_len)

    d_trace = get_domains(p, w_trace, d_trace_len)
    d_lde = get_domains(p, w_lde, d_lde_len)
    d_ev = get_domains(p, w_ev, d_ev_len)

    boundary_target_degree = d_ev_len - (d_trace_len - 1)
    transition_target_degree = d_ev_len - 2
    constraint_target_degree = d_ev_len - d_trace_len  # after denominators divided out
    composition_target_degree = constraint_target_degree - 1

    boundary_adj_degree = boundary_target_degree - get_degree(tx)
    boundary_adj = adj_poly(boundary_adj_degree)
    transition_adj_degree = transition_target_degree - get_degree(tx)
    transition_adj = adj_poly(transition_adj_degree)

    ood_x2 = pf.mul(ood_x, w_trace)
    ood_x3 = pf.mul(ood_x2, w_trace)
    composition_adj_degree = constraint_target_degree - get_degree(tx)
    composition_adj = adj_poly(composition_adj_degree)

    # recover composition polynomial evaluations
    ood_x_val = pf.eval_poly_at(tx, ood_x)
    ood_x2_val = pf.eval_poly_at(tx, ood_x2)
    ood_x3_val = pf.eval_poly_at(tx, ood_x3)

    # (1) directly evaluate cx over ood_x, (2) recover ood_x_cval from tx, i.e., rebuild ood_x_cval from tx
    # if (1) doesn't match (2), the verification will end up in a failure.
    ood_x_cval = pf.eval_poly_at(cx, ood_x) # direct evaluation

    re_icx = pf.sub(ood_x_val, 1)
    re_icx = pf.add(re_icx, pf.mul(re_icx, pf.eval_poly_at(boundary_adj, ood_x)))
    re_icx = pf.div(re_icx, pf.sub(ood_x, 1))  # input constraint: (t(ood_x) - 1) / (ood_x - 1)
    
    re_ocx = pf.sub(ood_x_val, 34)
    re_ocx = pf.add(re_ocx, pf.mul(re_ocx, pf.eval_poly_at(boundary_adj, ood_x)))
    re_ocx = pf.div(re_ocx, pf.sub(ood_x, d_trace[7]))

    re_tcx_denom = 1  # transition constraint: denom = (ood_x)
    for i in range(d_trace_len - 2):
        re_tcx_denom = pf.mul(re_tcx_denom, pf.sub(ood_x, d_trace[i]))
    re_tcx_num = pf.sub(pf.add(ood_x_val, ood_x2_val), ood_x3_val)
    re_tcx_num = pf.add(re_tcx_num, pf.mul(re_tcx_num, pf.eval_poly_at(transition_adj, ood_x)))
    re_tcx = pf.div(re_tcx_num, re_tcx_denom)
    re_ood_x_cval = pf.add(pf.add(re_icx, re_ocx), re_tcx) # rebuild it from tx and constrain expressions
    print("[VERIFIER][test] constraint eval at ood_x check:", re_ood_x_cval == ood_x_cval)
    # If they do not match, the following test will fail.

    cp_t1_ev = [pf.sub(pf.eval_poly_at(tx, x), ood_x_val) for x in d_lde]
    cp_t1_ev = [pf.div(y, pf.sub(x, ood_x)) for x, y in zip(d_lde, cp_t1_ev)]

    cp_t2_ev = [pf.sub(pf.eval_poly_at(tx, x), ood_x2_val) for x in d_lde]
    cp_t2_ev = [pf.div(y, pf.sub(x, ood_x2)) for x, y in zip(d_lde, cp_t2_ev)]

    cp_t3_ev = [pf.sub(pf.eval_poly_at(tx, x), ood_x3_val) for x in d_lde]
    cp_t3_ev = [pf.div(y, pf.sub(x, ood_x3)) for x, y in zip(d_lde, cp_t3_ev)]

    cp_t_ev = [pf.add(pf.add(x, y), z) for x, y, z in zip(cp_t1_ev, cp_t2_ev, cp_t3_ev)]
    cp_t_ev = [pf.add(y, pf.mul(y, pf.eval_poly_at(composition_adj, x))) for x, y in zip(d_lde, cp_t_ev)]

    cp_c_ev = [pf.sub(pf.eval_poly_at(cx, x), re_ood_x_cval) for x in d_lde]
    cp_c_ev = [pf.div(y, pf.sub(x, ood_x)) for x, y in zip(d_lde, cp_c_ev)]

    recover_cp_ev = [pf.add(x, y) for x, y in zip(cp_t_ev, cp_c_ev)] # rebuilt from everyting, this is what needs to be passed on to FRI.
    recover_cp = trim_poly(pf.lagrange_interp(d_lde, recover_cp_ev))

    # bounded degree check. [TODO] use FRI
    print("[VERIFIER] the bounded degree check on composition poly:", get_degree(recover_cp) <= composition_target_degree)

    # [TEST] random query check simulation (10 times)
    query_check_sim_res = True
    for i in range(10):
        idx = random.randrange(1, 120)
        if recover_cp_ev[idx] != cp_ev[idx]:
            print("[VERIFIER][test] random query check simualtion fail at", i, idx)
            query_check_sim_res = False
            break
    if query_check_sim_res:
        print("[VERIFIER][test] random query check simualtion passed")

if __name__ == "__main__":
    p = 257
    max_divisor = 256
    g = 3
    blowup = 16
    pf = PrimeField(p)

    # example-1: small fibonacci
    trace = [1, 2, 3, 5, 8, 13, 21, 34]  # len=8
    trace_error_input = [2, 2, 3, 5, 8, 13, 21, 34]   # attack-1: input constraint violation, t[0] = 1 --> 2
    trace_error_output = [1, 2, 3, 5, 8, 13, 21, 35]  # attack-2: output constraint violation, t[7] = 34 --> 35
    trace_error_transition = [1, 2, 3, 5, 9, 13, 21, 34]  # attack-3: transition constraint violation, t[4] = 8 --> 9

    # 1. take into account only transition constraint
    if 1 == 2:
        tx, px, dx = prove_small_fib_transition_constraint(p, g, blowup, trace)
        verify_small_fib_transition_constraint(p, g, blowup, tx, px, dx)

    # 2. consider all
    if 1 == 2:
        tx, cx, ood_x, cp_ev = prove_small_fib_constraint_all(p, g, blowup, trace)
        verify_small_fib_constraint_all(p, g, blowup, tx, cx, ood_x, cp_ev)
    
    # 3. attack-1: forcing degree get lower
    if 1 == 2:
        tx, cx, ood_x, cp_ev = prove_small_fib_constraint_all(p, g, blowup, trace)
        # trace_error_input leads to cx having a larger degree than it has to be.
        # len(cx) has to be 57 so this attack forcely changes len(cx) to 57.
        # -- result: attack not detected because my codes currenly are checking the degree only.
        #            which means I'm not verifying whether tx and cx are correcly linked.
        #            What I'm not understanding now is-- intuition of how to check the correctness of tx and cx.
        # -- try-1: feed traces and eval constraints instead of tx and cx.
        while True:
            cx.pop()
            if len(cx) <= 57:
                break
        verify_small_fib_constraint_all(p, g, blowup, tx, cx, ood_x, cp_ev)

    # 4. attack-2: get values from the result of authentic prove attempt and simply replay it
    if 1 == 1:
        tx_au, cx_au, ood_x_au, cp_ev_au = prove_small_fib_constraint_all(p, g, blowup, trace) # get authentic ones
        tx, cx, ood_x, cp_ev = prove_small_fib_constraint_all(p, g, blowup, trace_error_transition) # error
        verify_small_fib_constraint_all(p, g, blowup, tx, cx, ood_x, cp_ev_au) # tx-cx are not linked with cp_ev_au

    print("all success")