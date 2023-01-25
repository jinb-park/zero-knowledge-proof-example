import poly
from poly import PrimeField
import random
import sys

def get_root_of_unity(p, g, dlen):
    pf = PrimeField(p)
    root_of_unity = pow(g, (p-1)//dlen, p)
    return root_of_unity

def get_domains(p, w, dlen):
    return [pow(w, i, p) for i in range(dlen)]

def trim_poly(p):
    rp = p.copy()
    rp.reverse()
    for c in rp:
        if c == 0:
            del p[-1]
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
    assert (len(cx)-1) <= target_bound_degree
    print("verification success!") 


def prove_small_fib_constraint(p, g, blowup, trace):
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

    # NOTE for input constraint
    # -- P(x) = T(x) - v  --> P(x) is an input constraint function
    # -- P(x) = T(x) - 1 && P(x) = C(x) * D(x)  --> C(x) is a constraint polynomial for the input constraint
    # -- Constraint: P(x) must be 0 where x = w_trace_0 = 1.
    # -- As P(x) = C(x) * D(x), C(x) * D(x) must be 0 where x = w_trace_0 = 1
    # -- "D(x) = (x-1)" satisfies the condition.
    # -- P(x) = C(x) * (x-1) --> C(x) = P(x) / (x-1)
    # -- deg(P) = deg(C) + 1

    # 3. input constraint function evaluations
    # [Q] maybe I'm doing something wrong here.. how to evaluate input constraint function? P(x)=T(x)-2
    # [Q] This is the key part--!! Think a target-degree first way-!
    #     input_constraint_target_degree = (trace_len * max_constraint_degree) - trace_len + 1
    #     if P(x) is of degree 3, we have to add adjustment degree-! [Q] Why target-degree matters?
    #
    # [KEY QUESTION] max_constraint_degree and target_degree have to do with read-solomon codes and its coding rate--!
    #                I have to see this in the context of RS codes and write an article for that. (use of RS codes in STARK article)
    # [KEY QUESTION] though, getting how to use remainder to verify constraints might be enough to catch on to its overall flow--! (STARK article)

    # NOTE for target degree (only in the small fib example)
    # -- boundary_target_degree? --> boundary only considers the first and the last independently. i.e., -(d_trace_len-1) means excluding the boundary-!
    # -- transition_target_degree? --> transition considers all traces except the last two. because in small fib example,
    #    t[6]+t[7]-t[8]=0 --> t[8] is out of index--! so, t[6] and t[7] must be excluded-!
    boundary_target_degree = d_ev_len - (d_trace_len - 1)
    transition_target_degree = d_ev_len - 2
    constraint_target_degree = d_ev_len - d_trace_len  # after denominators divided out

    #########################
    # boundary constraint
    #########################
    # px1: for constraint t[0]-1=0 (intput constraint)
    stride = (int)(blowup / max_constraint_degree)
    #trace_lde[0] = 2  # --> violating the input constraint. trace_lde[0] == trace[0], this attack holds trace as it but corrupts trace_lde!
    px1_ev = [pf.sub(x, 1) for x in trace_lde[::2]]
    px1 = trim_poly(pf.lagrange_interp(d_ev, px1_ev))
    boundary_adj_degree = boundary_target_degree - len(px1)
    px1_adj = pf.mul_polys(px1, adj_poly(boundary_adj_degree))
    cx1 = pf.add_polys(px1, px1_adj)    # linear combination with constant values (1, 1)
    cpx1 = pf.div_polys(cx1, [-1, 1])   # denominator: (x-1) where 1 is w_trace_0 (the first x)1
    #assert len(cpx1) == (boundary_target_degree - 1)  # check--!

    # low-level check
    # check: px1 must be divisible by (x-1). no remainder left.
    # [KEY QUESTION] How to adjust it to the low-degree testing of FRI?
    px1_ev_low = [pf.sub(x, 1) for x in trace]
    px1_low = trim_poly(pf.lagrange_interp(d_trace, px1_ev_low))
    cx1_low = pf.div_polys(px1_low, [-1, 1])
    print(pf.mul_polys(cx1_low, [-1, 1]) == px1_low)

    # px2: for constraint t[7]-34=0 (output constraint)
    #trace_lde[112] = 37  # --> violating the output constraint. trace[7] == trace_lde[7 * blowup(16)]  (7*16=112)
    px2_ev = [pf.sub(x, 34) for x in trace_lde[::2]]
    px2 = trim_poly(pf.lagrange_interp(d_ev, px2_ev))
    px2_adj = pf.mul_polys(px2, adj_poly(boundary_adj_degree))
    cx2 = pf.add_polys(px2, px2_adj)
    cpx2 = pf.div_polys(cx2, [-d_trace[7], 1])  # denominator: (x - d_trace[7]) where d_trace[7] is the last x
    #assert len(cpx2) == (boundary_target_degree - 1)

    # cpx_boundary: the final single boundary constraint polynomial
    cpx_boundary = pf.add_polys(cpx1, cpx2)  # linear combination. [Q] randomness required?
    # -- check-1: degree check
    if len(cpx_boundary) != (constraint_target_degree): print("cpx_boundary degree check fail")
    # -- check-2: zero-value check (remainder check)
    for i in range(len(px1) - 1, len(cpx_boundary) - len(px1) + 1):
        if cpx_boundary[i] != 0:
            print("cpx_boundary value check fail")
            break

    #########################
    # transition constraint
    #########################
    # t[i]+t[i+1]=t[i+2] --> t[i]+t[i+1]-t[i+2]=0 --> the last i = trace_len - 2 - 1 (5)
    # t(x) + t(g*x) - t(g^2*x) = 0 --> i+n == g^n * x
    # denominator (d(x)): (x-w_trace_0)(x-w_trace_1)...(x-w_trace_n-1) n = 8 here.
    # p(x) = c(x) * d(x)  --> p(x) = t(x) + t(g*x) - t(g^2*x)
    #
    # for trace[0]-[1]-[2] --> trace_lde[0]-[16]-[32]
    # ... lde domain ....  --> trace_lde[1]-[17]-[33]
    # for trace[1]-[2]-[3] --> trace_lde[16]-[32]-[48]
    # ... lde domain ....  --> trace_lde[17]-[33]-[49]
    # for trace[5]-[6]-[7] --> trace_lde[80]-[96]-[112]
    # ... lde domain ...   --> trace_lde[95]-[111]-[127]

    input_list = []
    for i in range(0, len(trace_lde) - 2*blowup, 2):
        input_list.append((trace_lde[i], trace_lde[i+blowup], trace_lde[i+blowup*2]))
    tpx_ev = [pf.sub(pf.add(x[0], x[1]), x[2]) for x in input_list]
    tpx = trim_poly(pf.lagrange_interp(d_ev[0:len(tpx_ev)], tpx_ev))
    transition_adj_degree = transition_target_degree - len(tpx)
    tpx_adj = pf.mul_polys(tpx, adj_poly(transition_adj_degree))

    # get a denominator
    tpx_denom = [1]
    for i in range(d_trace_len - 2):
        tpx_denom = pf.mul_polys(tpx_denom, [-d_trace[i], 1])
    tcx = pf.add_polys(tpx, tpx_adj)
    cpx = pf.div_polys(tcx, tpx_denom)
    # NOTE: why is cpx of degree 2? --> because in fibonacci example there are three values involved in a transition,
    #       which means interpolating them would end up of degree 2. --> [Q] right? it's something wrong. revisit here-!
    #       [REVISIT]
    # NOTE for max_constraint_degree --> max_constraint_degree=8 means nine values at most can be involved in a transition.

    # (1) symbolic evaluations
    '''
    tpx_symbol = [0]
    tpx_symbol = pf.add_polys(tpx_symbol, tx)
    tmp_poly = tx.copy()
    for i in range(1, len(tmp_poly)): tmp_poly[i] = pf.mul(tmp_poly[i], w_trace)
    tpx_symbol = pf.add_polys(tpx_symbol, tmp_poly)
    tmp_poly = tx.copy()
    for i in range(1, len(tmp_poly)): tmp_poly[i] = pf.mul(tmp_poly[i], pf.exp(w_trace, 2))
    tpx_symbol = pf.sub_polys(tpx_symbol, tmp_poly)
    tcx_symbol = pf.div_polys(tpx_symbol, tpx_denom)

    bcx_symbol = pf.sub_polys(tx, [1])
    bcx_symbol2 = pf.div_polys(bcx_symbol, [-1, 1])
    bcx_ev_low = [pf.mul(pf.eval_poly_at(bcx_symbol2, x), pf.eval_poly_at([-1, 1], x)) for x in d_ev]
    bcx_low = trim_poly(pf.lagrange_interp(d_ev, bcx_ev_low))
    print(tx)
    '''

    # low-level check
    # check: tpx must be divisible by tpx_denom
    input_list_low = []
    for i in range(0, len(trace_lde) - 2*blowup, 2):
        input_list_low.append((trace_lde[i], trace_lde[i+blowup], trace_lde[i+blowup*2]))
    tpx_ev_low = [pf.sub(pf.add(x[0], x[1]), x[2]) for x in input_list_low]
    tpx_low = trim_poly(pf.lagrange_interp(d_ev[:len(tpx_ev_low)], tpx_ev_low))
    #tpx_low = pf.mul_polys(tpx_low, [0, 0, 0, 0, 0, 0, 0, 0, 1])  # adjustment degree: * x^8

    # consistency check between T(x) and C(x)
    #ood_i = 71
    ood_x = 254
    left_ev = pf.sub(pf.add(pf.eval_poly_at(tx, ood_x), pf.eval_poly_at(tx, pf.mul(ood_x, w_trace))), pf.eval_poly_at(tx, pf.mul(ood_x, pf.exp(w_trace, 2))))
    right_ev = pf.eval_poly_at(tpx_low, ood_x)
    #left_ev = pf.sub(pf.add(pf.eval_poly_at(tx, d_lde[ood_i]), pf.eval_poly_at(tx, d_lde[ood_i+blowup])), pf.eval_poly_at(tx, d_lde[ood_i+blowup*2]))
    #right_ev = pf.eval_poly_at(tpx_low, d_lde[ood_i])
    print(left_ev == right_ev)

    # method-1: checking if evaluations go zero
    for i, x in enumerate(tpx_ev_low):
        if i % 8 == 0 and x != 0: print("evaluation error!")

    # method-2: bound degree check: the final degree must be 1. deg(P) = deg(C) * deg(D), deg(D)=6, deg(P)=7
    # only 42 points-: how to get it up to 128 points?
    tcx_ev_low = []
    tcx_ev_low_d = []
    for x, y in zip(d_ev[:len(tpx_ev_low)], tpx_ev_low):
        denom = pf.eval_poly_at(tpx_denom, x)
        if denom != 0:
            tcx_ev_low.append(pf.div(y, denom))
            tcx_ev_low_d.append(x)
    tcx_ev = trim_poly(pf.lagrange_interp(tcx_ev_low_d, tcx_ev_low))
    print(len(tcx_ev))
    #tcx_low = pf.div_polys(tpx_low, tpx_denom)

    # method-3: bound degree check with 128 points (lde domain size)
    # P'(x) = C(x) - C(ood_x), P'(x) = C'(x) * (x - ood_x), C'(x) = P'(x) / (x - ood_x)
    cppx_ev = [pf.div( (pf.sub(pf.eval_poly_at(tcx_ev, x), pf.eval_poly_at(tcx_ev, ood_x))), (pf.sub(x, ood_x)) ) for x in d_lde]
    cppx = trim_poly(pf.lagrange_interp(d_lde, cppx_ev))
    print(len(cppx_ev))
    print(len(cppx))

    '''
    ood_points = []
    for i in range(256):
        found = False
        for x in d_lde:
            if i == x:
                found = True
                break
        if found == False:
            ood_points.append(i)
    print(ood_points)
    print(len(ood_points))
    '''

    ##################################
    # first consistency check: P(x) (trace[2]+trace[3]-trace[4] = 0) = C(x) * D(x)
    #print(pf.sub(pf.add(pf.eval_poly_at(tx, d_trace[2]), pf.eval_poly_at(tx, d_trace[3])), pf.eval_poly_at(tx, d_trace[4])))
    #print(pf.mul(pf.eval_poly_at(tcx_low, d_trace[2]), pf.eval_poly_at(tpx_denom, d_trace[2])))

    # second consistency check: P(x) (trace[0]+trace[1]-trace[2] = 0) = C(x) * D(x)
    #print(pf.sub(pf.add(pf.eval_poly_at(tx, d_trace[0]), pf.eval_poly_at(tx, d_trace[1])), pf.eval_poly_at(tx, d_trace[2])))
    #print(pf.mul(pf.eval_poly_at(tcx_low, d_trace[0]), pf.eval_poly_at(tpx_denom, d_trace[0])))

    # weakness of existing point check --> If we choose index-0 (not corrupted index-2), it will pass--! if x=0~7, 1/8(d_trace_len) attack possibility..
    # solution: larger domain and out-of-domain 'x' --> much low attack possibility... 1/(d_trace_len * blowup) == 1/d_lde_len
    # ood consistency check. as long as "ood_i" is randomly chosen, it will be secure.
    #ood_i = 71
    #left_ev = pf.sub(pf.add(pf.eval_poly_at(tx, d_lde[ood_i]), pf.eval_poly_at(tx, d_lde[ood_i+blowup])), pf.eval_poly_at(tx, d_lde[ood_i+blowup*2]))
    #right_ev = pf.mul(pf.eval_poly_at(tcx_low, d_lde[ood_i]), pf.eval_poly_at(tpx_denom, d_lde[ood_i]))
    #print(left_ev == right_ev)

    # proof scenario with ood consistency check
    # (1) [P] send traces (or tx), constraint expressions (P(x)=t(x)+t(x*g)-t(x*g^2)), denom (transition denom)
    # (2) [V] retrieve constraint evaluations (cx_ev)
    # (3) [P] P(x) = C(x)*D(x) ==> consistency check evaluations
    # (4) [V] check consistency (0 at ood index)

    # turn it into a polynomial (for non-interactiveness)
    # turn it into the condition of the bounded degree
    # P'(x) = C(x) - C(z),  P'(x) = C'(x) * (x - z), C'(x) = P'(x) / (x - z)

    ####################################


    cpx_transition = cpx  # because there is no other transition polynomials here-!
    if len(cpx_transition) != (constraint_target_degree): print("cpx_transition degree check fail")  # -- check-1: degree check
    # -- check-2: value check (remainder check)
    for i in range(2, len(cpx_transition) - 2):
        if cpx_transition[i] != 0:
            print("cpx_transition value check fail")
            break

    # the final composition constraint polynomial (ccx)
    ccx = pf.add_polys(cpx_boundary, cpx_transition)

    ##########################################################################
    # DEEP composition polynomial: combining trace and constraint polynomials into a single one
    # -- [TODO] understand why it is designed this way
    # -- [TODO**] review https://medium.com/starkware/starkdex-deep-dive-the-stark-core-engine-497942d0f0ab
    ##########################################################################
    # DEEP composition polynomial, dp(x)
    # ccx: composition constraint poly
    # tx: trace poly
    # The aim is to create a linear combination of ccx and tx.
    # [Q] How to check security DEEP point offers?
    #     -- I mean, what attack can end up undetectable if DEEP point method is not used?
    ood_z = d_lde[d_trace_len + 5] # [TODO] use prng with the seed from the previous step-!
    ood_zn = pf.mul(ood_z, w_trace)
    ood_zn2 = pf.mul(ood_zn, w_trace)
    dcp_target_degree = d_ev_len - d_trace_len - 1  # why? this is equal to deg(composition constraint poly)-1.
    zv = pf.eval_poly_at(tx, ood_z)
    znv = pf.eval_poly_at(tx, ood_zn)
    znv2 = pf.eval_poly_at(tx, ood_zn2) # we need three points as our transition constraint involves in three points.

    # dtx, working domain: d_trace
    # dtx1's denom: (x - zv)
    # dtx2's denom: (x - znv)
    # dtx3's denom: (x - znv2)
    dtx1_ev = [pf.sub(x, zv) for x in trace]
    dtx1 = trim_poly(pf.lagrange_interp(d_trace, dtx1_ev))
    dtx2_ev = [pf.sub(x, znv) for x in trace]
    dtx2 = trim_poly(pf.lagrange_interp(d_trace, dtx2_ev))
    dtx3_ev = [pf.sub(x, znv2) for x in trace]
    dtx3 = trim_poly(pf.lagrange_interp(d_trace, dtx3_ev))
    dtx1 = pf.div_polys(dtx1, [-zv, 1])
    dtx2 = pf.div_polys(dtx2, [-znv, 1])
    dtx3 = pf.div_polys(dtx3, [-znv2, 1])

    dtx = pf.add_polys(dtx1, dtx2)
    dtx = pf.add_polys(dtx, dtx3)
    dtx_adj_degree = dcp_target_degree - len(dtx1) + 1
    dtx_adj = pf.mul_polys(dtx1, adj_poly(dtx_adj_degree))
    dtx = pf.add_polys(dtx, dtx_adj)

    # dcx
    zcv = pf.eval_poly_at(ccx, ood_z)
    dcx = ccx.copy()
    dcx[0] = pf.sub(dcx[0], zcv)
    dcx = pf.div_polys(dcx, [-zcv, 1])

    # the final dpx
    dpx = pf.add_polys(dtx, dcx)
    dpx_ev = [pf.eval_poly_at(dpx, x) for x in d_lde]
    assert dcp_target_degree == len(dpx) - 1

    # return a proof object consisting of a variety of data necessary to verify
    # [TODO] use merkle tree and PRNG
    # dpx: deep composition polynomial
    # dpx_ev: evaluations of dpx
    # trace: trace 
    return (dpx, dpx_ev, trace)

def verify_small_fib_constraint():
    # now, inspect all points rather than picking out random points
    # [Q] at a high level, how does this verify work?
    pass

if __name__ == "__main__":
    p = 257
    max_divisor = 256
    g = 3
    blowup = 16

    # example-1: small fibonacci
    trace = [1, 2, 3, 5, 8, 13, 21, 34]  # len=8
    trace_error_input = [2, 2, 3, 5, 8, 13, 21, 34]   # attack-1: input constraint violation, t[0] = 1 --> 2
    trace_error_output = [1, 2, 3, 5, 8, 13, 21, 35]  # attack-2: output constraint violation, t[7] = 34 --> 35
    trace_error_transition = [1, 2, 3, 5, 9, 13, 21, 34]  # attack-3: transition constraint violation, t[4] = 8 --> 9

    #px, px_ev, ptrace = prove_small_fib_constraint(p, g, blowup, trace)

    tx, px, dx = prove_small_fib_transition_constraint(p, g, blowup, trace_error_transition)
    verify_small_fib_transition_constraint(p, g, blowup, tx, px, dx)

    print("all success")