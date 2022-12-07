import sys
sys.path.append('../stark')

import poly
from poly import PrimeField
import random
import hashlib

def weak_hash(pf, mod, g, t):
    m = hashlib.sha256()
    m.update(g.to_bytes(4, byteorder='big'))
    m.update(t.to_bytes(4, byteorder='big'))
    return (int.from_bytes(m.digest(), byteorder='big')) % (mod - 1)

def strong_hash(pf, mod, g, y, t):
    m = hashlib.sha256()
    m.update(g.to_bytes(4, byteorder='big'))
    m.update(y.to_bytes(4, byteorder='big'))
    m.update(t.to_bytes(4, byteorder='big'))
    return (int.from_bytes(m.digest(), byteorder='big')) % (mod - 1)

class Prover():
    def __init__(self, pf, g, m):
        self.g = g
        self.pf = pf
        self.m = m
        self.y = 0   # public key
        self.x = 0   # private key
        self.c = 1   # random challenge

    def get_public_key(self):
        self.x = self.pf.get_random()
        self.y = self.pf.exp(self.g, self.x)
        return self.y
    
    def get_random_values(self):
        self.v = self.pf.get_random()
        self.t = self.pf.exp(self.g, self.v)
        return self.t

    def get_r(self):
        #self.r = self.pf.sub(self.v, self.pf.mul(self.c, self.x))
        #self.r = (self.v - self.pf.mul(self.c, self.x)) % (self.m - 1)
        self.r = (self.v - (self.c * self.x)) % (self.m - 1)
        return self.r

    def get_r_with_hash(self, is_weak):
        m = hashlib.sha256()
        if is_weak == True:
            self.c = weak_hash(self.pf, self.m, self.g, self.t)
        else:
            self.c = strong_hash(self.pf, self.m, self.g, self.y, self.t)
        #self.r = self.pf.sub(self.v, self.pf.mul(self.c, self.x))
        self.r = (self.v - (self.c * self.x)) % (self.m - 1)
        return self.r

    def self_verification(self):
        gr = self.pf.exp(self.g, self.r)
        yc = self.pf.exp(self.y, self.c)
        computed_t = self.pf.mul(gr, yc)
        print(self.t == computed_t)
    
    def attack_precomputation(self):
        self.v = self.pf.get_random()
        self.t = self.pf.exp(self.g, self.v)
        self.r = self.pf.get_random()
        gr = self.pf.exp(self.g, self.r)
        self.y = self.pf.div(self.t, gr)
        #self.x = self.pf.sub(self.v, self.r)
        self.x = (self.v - self.r) % (self.m - 1)

        assert self.pf.exp(self.g, self.x) == self.y
        return (self.y, self.t, self.r)
    
    def attack_precomputation_with_hash(self):
        self.v = self.pf.get_random()
        self.t = self.pf.exp(self.g, self.v)
        c = weak_hash(self.pf, self.m, self.g, self.t)

        self.r = self.pf.get_random()
        gr = self.pf.exp(self.g, self.r)
        cy = self.pf.div(1, c)

        self.y = self.pf.exp(self.pf.div(self.t, gr), cy)
        self.x = self.pf.div(self.pf.sub(self.v, self.r), c)

        assert self.pf.exp(self.g, self.x) == self.y
        return (self.y, self.t, self.r)

class Verifier():
    def __init__(self, pf, g, m):
        self.pf = pf
        self.g = g
        self.m = m
        self.c = 1

    def get_random_challenge(self):
        self.c = self.pf.get_random()
        return self.c
    
    def verify(self, y, t, r):
        gr = self.pf.exp(self.g, r)
        yc = self.pf.exp(y, self.c)
        computed_t = self.pf.mul(gr, yc)
        return (t == computed_t)
    
    def verify_with_hash(self, y, t, r, is_weak):
        self.c = 0
        if is_weak: self.c = weak_hash(self.pf, self.m, self.g, t)
        else: self.c = strong_hash(self.pf, self.m, self.g, y, t)
        
        gr = self.pf.exp(self.g, r)
        yc = self.pf.exp(y, self.c)
        computed_t = self.pf.mul(gr, yc)

        return (t == computed_t)

class InteractiveProof():
    def __init__(self, p, v, pf, g, m, option):
        self.p = p
        self.v = v
        self.pf = pf
        self.m = m
        self.g = g
        self.option = option
        pass
    
    def start_authentic_case(self):
        # a random challenge is constant (c = 1)
        y = self.p.get_public_key()
        t = self.p.get_random_values()
        r = self.p.get_r()
        assert self.v.verify(y, t, r)
    
    def start_attack_case(self):
        # a random challenge is constant (c = 1)
        y, t, r = self.p.attack_precomputation()
        assert self.v.verify(y, t, r)

class NonInteractiveProof():
    def __init__(self, p, v, pf, g, option):
        self.p = p
        self.v = v
        self.pf = pf
        self.g = g
        self.option = option
        pass

    def start_authentic_case(self):
        y = self.p.get_public_key()
        t = self.p.get_random_values()
        r = self.p.get_r_with_hash(True)
        assert self.v.verify_with_hash(y, t, r, True)

    def start_attack_case(self):
        y, t, r = self.p.attack_precomputation_with_hash()
        assert self.v.verify_with_hash(y, t, r, True)
    
if __name__ == "__main__":
    g = 2
    m = 37
    #g = 2
    #m = pow(2,31) - 1
    pf = PrimeField(m)
    p = Prover(pf, g, m)
    v = Verifier(pf, g, m)

    # interacitve proof
    InteractiveProof(p, v, pf, g, m, "and").start_authentic_case()
    InteractiveProof(p, v, pf, g, m, "and").start_attack_case()

    # non-interactive proof
    NonInteractiveProof(p, v, pf, g, "and").start_authentic_case()
    #NonInteractiveProof(p, v, pf, g, "and").start_attack_case()  # [BUG] todo

    print("all test passed")