import poly
from poly import PrimeField
import random

class FriProof():
    def __init__(self, xs0, ys0, fx0):
        self.xs_list = []
        self.ys_list = []
        self.fx_list = []
        self.a_list = []
        self.xs_list.append(xs0)
        self.ys_list.append(ys0)
        self.fx_list.append(fx0)

    def add_random_a(self, a):
        self.a_list.append(a)

    def load_random_a(self, i):
        return self.a_list[i]

    def add_next_layer(self, xs, ys, fnx):
        self.xs_list.append(xs)
        self.ys_list.append(ys)
        self.fx_list.append(fnx)

    def load_layer(self, i):
        if i >= len(self.xs_list):
            return (None, None, None)
        return (self.xs_list[i], self.ys_list[i], self.fx_list[i])
    
    def load_last_layer(self):
        return (self.xs_list[-1], self.ys_list[-1], self.fx_list[-1])

    def print(self):
        for i in range(len(self.xs_list)):
            print("xs[" + str(i) + "] ", self.xs_list[i], " // ys[" + str(i) + "] ", self.ys_list[i])

class Fri():
    def __init__(self, modulus, fx, w, type, xs = None):
        self.modulus = modulus
        self.fx = fx
        self.w = w
        if xs == None:
            self.xs0 = [pow(self.w, i, self.modulus) for i in range(self.n)]
            self.n = self.modulus - 1
        else:
            self.xs0 = xs.copy()
            self.n = len(self.xs0)
        self.type = type  # type = {"constant", "interactive", "noninteractive"}
        self.pf = PrimeField(self.modulus)
        self.ys0 = [self.pf.eval_poly_at(self.fx, x) for x in self.xs0]
        #print(self.ys0)
        self.proof = FriProof(self.xs0, self.ys0, self.fx)

    def set_type(self, type):
        self.type = type

    def reduce(self, fx): # degree reduction, currently d = d/2, i.e., reduced by a factor of 2
        # f(x) = g(x^2) + x*h(x^2) --> FFT-like reduction
        gx = []
        hx = []
        for i, c in enumerate(fx):
            if i % 2 == 0: # even coefficients
                hx.append(c)
            else: # odd coefficients
                gx.append(c)
        
        # f_next(x) = g(x) + a*h(x) where 'a' depends on its proof type [TODO]
        fnx = []
        a = 1
        # a = 1 --> fn(x) = g(x) + h(x)
        for i in range(len(gx)):
            if self.type == "constant":
                a = 1
            elif self.type == "interactive": # NOTE: just simulating interactive. it's not a real interactive mode.
                a = random.randrange(999)
            else:
                a = 1  # [TODO] # non-interactive, use of hash function
            fnx.append(self.pf.add(gx[i], self.pf.mul(hx[i], a)))
        return fnx, a
    
    def print_proof(self):
        self.proof.print()

    def prove(self):  # prover
        fx = self.fx
        w = self.w
        n = self.n

        while True:
            fnx, a = self.reduce(fx)
            # compute next domain
            w = self.pf.mul(w, w)  # w = w^2
            n = self.pf.div(n, 2)
            xs = [pow(w, i, self.modulus) for i in range(n)]
            # eval
            ys = [self.pf.eval_poly_at(fnx, x) for x in xs]
            # add xs-ys into proof
            self.proof.add_next_layer(xs, ys, fnx)
            self.proof.add_random_a(a)

            print(ys)

            if len(fnx) <= 1:  # exit condition is not configurable at this time
                break
            fx = fnx  # update fx
    
    def verify(self):  # verifier
        xs = self.xs0
        ys = self.ys0
        fx = self.fx
        idx = 1
        ys_verified_list = []
        ys_verified_list.append(ys)

        while True:
            ys_verified = []
            xs_next, ys_next, _ = self.proof.load_layer(idx)
            if xs_next == None:
                break
            a = self.proof.load_random_a(idx-1)

            next_n = len(xs_next)
            for i, x in enumerate(xs):
                if i >= next_n:
                    break
                y = ys[i]  # e.g., xs[1]=3, ys[1]=f(3), xs[1+8]=..., ys[1+8]=f(-3)
                my = ys[i + next_n]
                gx2 = self.pf.div(self.pf.add(y, my), 2)
                hx2 = self.pf.div(self.pf.sub(y, my), self.pf.mul(x, 2))
                # [TODO] no random value at this time
                fn = self.pf.add(gx2, self.pf.mul(hx2, a))
                ys_verified.append(fn)

            # layer value check--!
            #for i in range(len(ys_verified)):
            #    if ys_verified[i] != ys_next[i]:
            #        print("error: layer-" + str(idx) + " value mismatch")
            #        return False  # skip for now

            ys_verified_list.append(ys_verified)
            xs = xs_next
            ys = ys_verified
            idx += 1
        
        print(ys_verified_list)

        # remainder value check--! 
        xs_last, ys_last, fx_last = self.proof.load_last_layer()
        if len(ys_verified_list[-1]) != len(ys_last):
            return False
        for i in range(len(ys_verified_list[-1])):
            if ys_verified_list[-1][i] != ys_last[i]:
                print("error: remainder value mismatch")
                return False
        
        # check if remainder values are of a low degree--!
        d = len(fx_last)
        interp_xs = xs_last[:d]
        interp_ys = ys_verified_list[-1][:d]
        poly = self.pf.lagrange_interp(interp_xs, interp_ys)
        for x, y in zip(xs_last[d:], ys_verified_list[-1][d:]):
            if self.pf.eval_poly_at(poly, x) != y:
                print("error: remainder values are not of a low degree")
                return False
            
        return True
    
    def corrupt(self, layer_idx, xs_idx, pair_attack):  # corruption test. assume a malicious prover here
        xs, ys, _ = self.proof.load_layer(layer_idx)
        if pair_attack == False:
            ys[xs_idx] = self.pf.add(ys[xs_idx], 1)
        else:
            # try to find a pair of values that will lead to correct values for the next layer
            # for now, try a brute-force strategy
            # plus, it's not considering random 'a' just to simulate the effectiveness of interactive mode.
            _, ys_next, _ = self.proof.load_layer(layer_idx + 1)
            n = len(ys)
            n_next = len(ys_next)
            xs_idx1 = xs_idx
            xs_idx2 = xs_idx + n_next  # pair = (xs_idx1, xs_idx2)
            ys1 = ys[xs_idx1]
            ys2 = ys[xs_idx2]
            target_g = self.pf.div(self.pf.add(ys1, ys2), 2)
            target_h = self.pf.div(self.pf.sub(ys1, ys2), self.pf.mul(xs[xs_idx], 2))
            target_g_h = self.pf.add(target_g, target_h)

            pair_found = False
            for i in range(self.modulus):
                for j in range(self.modulus):
                    g = self.pf.div(self.pf.add(i, j), 2)
                    h = self.pf.div(self.pf.sub(i, j), self.pf.mul(xs[xs_idx], 2))
                    if (i != ys1 or j != ys2) and (target_g_h == self.pf.add(g, h)):
                        print("pair found: ", i, j)
                        ys_next[xs_idx1 % n_next] = self.pf.add(ys_next[xs_idx1 % n_next], 1)
                        ys_next[xs_idx2 % n_next] = self.pf.add(ys_next[xs_idx2 % n_next], 1)
                        pair_found = True
                        break
                if pair_found == True:
                    break
            if pair_found == False:
                print("finding a pair for attack went wrong. attack failed")

def gen_fri_object():
    modulus = 17       # modulus is 17 for a finite field
    fx = (8, 2, 4, 1)  # fx = 8 + 2x + 4x^2 + x^3
    n = modulus - 1    # 16
    w = 3              # a primitive n-th root of unity (16-th root of unity)
    xs0 = [pow(w, i, modulus) for i in range(n)]  # first round domain
    fri = Fri(modulus, fx, w, "constant")
    return fri

def gen_fri_object_with_params(p, fx, w, xs):
    fri = Fri(p, fx, w, "constant", xs)
    return fri

def test_success_case():
    fri = gen_fri_object()
    fri.prove()
    assert fri.verify() == True

def test_attack_case_no_pair_attack():
    # 1. layer0
    fri = gen_fri_object()
    fri.prove()
    fri.corrupt(0, 1, False)
    assert fri.verify() == False

    # 2. layer1 (if num_query==0, it will go successful)
    fri = gen_fri_object()
    fri.prove()
    fri.corrupt(1, 2, False)
    assert fri.verify() == True

def test_attack_case_pair_attack():
    # 1. without random 'a'
    fri = gen_fri_object()
    fri.prove()
    fri.corrupt(0, 1, True)
    assert fri.verify() == True

    # 2. with random 'a' (i.e., interactive proof mode)
    fri = gen_fri_object()
    fri.set_type("interactive")
    fri.prove()
    fri.corrupt(0, 1, True)
    assert fri.verify() == False

def test_layer_construction():
    fx = (8, 2, 4)  # 8 + 2x + 4x^2
    pf = PrimeField(17)
    xs0 = [pow(3, i, 17) for i in range(16)]
    ys0 = [pf.eval_poly_at(fx, x) for x in xs0]
    xs1 = []
    ys1 = []
    #c = random.randrange(1, 15)
    c = 1

    for i in range(8):
        p1, p2 = ys0[i], ys0[i+8] 
        pi = pf.lagrange_interp((xs0[i], xs0[i+8]), (p1, p2)) # draw a line
        xs1.append(pf.mul(xs0[i], xs0[i]))
        ys1.append(pf.eval_poly_at(pi, c))

    print(ys0)
    print(xs1)
    print(ys1)

    # check low degree
    interp_xs1 = xs1[:2]
    interp_ys1 = ys1[:2]
    poly = pf.lagrange_interp(interp_xs1, interp_ys1)
    for x, y in zip(xs1[2:], ys1[2:]):
        if pf.eval_poly_at(poly, x) != y:
            print("error: it's not of a low degree")
    print("it's low degree!", poly, c)

if __name__ == "__main__":
    #test_success_case()
    #test_attack_case_no_pair_attack()
    #test_attack_case_pair_attack()

    #test_layer_construction()

    pf = PrimeField(17)
    for i in range(16):
        for j in range(16):
            aa = pf.div(pf.sub(i, j), 6)
            bb = pf.div(pf.add(i, j), 2)
            if pf.add(aa, bb) == 4:
                print(i, j)

    print("all test success")
