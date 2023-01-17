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

def test_small_fib_constraint(p, g, blowup, trace):
    # domain set-up
    pf = PrimeField(p)
    n = p - 1
    d_trace_len = len(trace)
    d_lde_len = d_trace_len * blowup
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
    cpx1 = pf.div_polys(cx1, [-1, 1])   # denominator: (x-1) where 1 is w_trace_0 (the first x)
    #assert len(cpx1) == (boundary_target_degree - 1)  # check--!

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
    assert len(cpx_boundary) == (boundary_target_degree - 1)  
    # -- check-2: zero-value check ([Q] remainder is not 0? right?)
    for i in range(len(px1) - 1, len(cpx_boundary) - len(px1) + 1):
        assert cpx_boundary[i] == 0  

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

    cpx_transition = cpx  # because there is no other transition polynomials here-!
    assert len(cpx_transition) == (transition_target_degree - len(tpx_denom) + 1)  # -- check-1: degree check
    # -- check-2: value check
    for i in range(2, len(cpx_transition) - 2):
        assert cpx_transition[i] == 0

    ##########################################################################
    # DEEP FRI: combining trace and constraint polynomials into a single one
    ##########################################################################

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

    test_small_fib_constraint(p, g, blowup, trace)

    print("all success")