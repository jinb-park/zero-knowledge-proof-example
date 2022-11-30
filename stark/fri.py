import poly
from poly import PrimeField

class FriProof():
    def __init__(self, xs0, ys0, fx0):
        self.xs_list = []
        self.ys_list = []
        self.fx_list = []
        self.xs_list.append(xs0)
        self.ys_list.append(ys0)
        self.fx_list.append(fx0)

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
    def __init__(self, modulus, fx, w, type):
        self.modulus = modulus
        self.fx = fx
        self.n = self.modulus - 1
        self.w = w
        self.xs0 = [pow(self.w, i, self.modulus) for i in range(self.n)]
        self.type = type  # type = {"constant", "interactive", "noninteractive"}
        self.pf = PrimeField(self.modulus)
        self.ys0 = [self.pf.eval_poly_at(self.fx, x) for x in self.xs0]
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
        # a = 1 --> fn(x) = g(x) + h(x)
        for i in range(len(gx)):
            fnx.append(self.pf.add(gx[i], hx[i]))
        return fnx
    
    def print_proof(self):
        self.proof.print()

    def prove(self):  # prover
        fx = self.fx
        w = self.w
        n = self.n

        while True:
            fnx = self.reduce(fx)
            # compute next domain
            w = self.pf.mul(w, w)  # w = w^2
            n = self.pf.div(n, 2)
            xs = [pow(w, i, self.modulus) for i in range(n)]
            # eval
            ys = [self.pf.eval_poly_at(fnx, x) for x in xs]
            # add xs-ys into proof
            self.proof.add_next_layer(xs, ys, fnx)
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
            xs_next, _, _ = self.proof.load_layer(idx)
            if xs_next == None:
                break

            next_n = len(xs_next)
            for i, x in enumerate(xs):
                if i >= next_n:
                    break
                y = ys[i]  # e.g., xs[1]=3, ys[1]=f(3), xs[1+8]=..., ys[1+8]=f(-3)
                my = ys[i + next_n]
                gx2 = self.pf.div(self.pf.add(y, my), 2)
                hx2 = self.pf.div(self.pf.sub(y, my), self.pf.mul(x, 2))
                # [TODO] no random value at this time
                fn = self.pf.add(gx2, hx2)
                ys_verified.append(fn)

            ys_verified_list.append(ys_verified)
            xs = xs_next
            ys = ys_verified
            idx += 1
        
        print(ys_verified_list)

        # remainder check--! 
        _, ys_last, _ = self.proof.load_last_layer()
        if len(ys_verified_list[-1]) != len(ys_last):
            return False
        for i in range(len(ys_verified_list[-1])):
            if ys_verified_list[-1][i] != ys_last[i]:
                return False
        return True
    
    def corrupt(self, layer_idx, xs_idx, pair_attack):  # corruption test. assume a malicious prover here
        _, ys, _ = self.proof.load_layer(layer_idx)
        if pair_attack == False:
            ys[xs_idx] = self.pf.add(ys[xs_idx], 1)
  
def test_success_case(fri):
    print(fri.verify())

def test_attack_case_no_pair_attack(fri):
    fri.corrupt(0, 1, False)
    print(fri.verify())

if __name__ == "__main__":
    modulus = 17       # modulus is 17 for a finite field
    fx = (8, 2, 4, 1)  # fx = 8 + 2x + 4x^2 + x^3
    n = modulus - 1    # 16
    w = 3              # a primitive n-th root of unity (16-th root of unity)
    xs0 = [pow(w, i, modulus) for i in range(n)]  # first round domain

    fri = Fri(modulus, fx, w, "constant")
    fri.prove()
    fri.print_proof()

    #test_success_case(fri)
    test_attack_case_no_pair_attack(fri)
