pragma circom 2.0.0;

template Num2Bits(n) {
    signal input in;
    signal output out[n];
    var lc1=0;

    var e2=1;
    for (var i = 0; i<n; i++) {
        out[i] <-- (in >> i) & 1;
        out[i] * (out[i] -1 ) === 0;
        lc1 += out[i] * e2;
        e2 = e2+e2;
    }

    lc1 === in;
}

template LessThan(n) {
    assert(n <= 252);  // 252 limitation? why?
    signal input in[2];
    signal output out;

    component n2b = Num2Bits(n+1);

    n2b.in <== in[0]+ (1<<n) - in[1];

    out <== 1-n2b.out[n];
}

template GreaterThan(n) {
    signal input in[2];
    signal output out;

    component lt = LessThan(n);

    lt.in[0] <== in[1];
    lt.in[1] <== in[0];
    lt.out ==> out;
}

/*
    Assume sel is binary.

    If sel == 0 then outL = L and outR=R
    If sel == 1 then outL = R and outR=L

 */
template Switcher() {
    signal input sel;
    signal input L;
    signal input R;
    signal output outL;
    signal output outR;

    signal aux;

    aux <== (R-L)*sel;    // We create aux in order to have only one multiplication
    outL <==  aux + L;
    outR <== -aux + R;
}

template Max(n) {
    signal input in[n];
    signal output out;

    component gts[n];        // store comparators
    component switchers[n+1];  // switcher for comparing maxs

    signal maxs[n+1];

    maxs[0] <== in[0];
    for(var i = 0; i < n; i++) {
        gts[i] = GreaterThan(252); // changed to 252 (maximum) for better compatibility
        switchers[i+1] = Switcher();

        gts[i].in[1] <== maxs[i];
        gts[i].in[0] <== in[i];

        switchers[i+1].sel <== gts[i].out;
        switchers[i+1].L <== maxs[i];
        switchers[i+1].R <== in[i];

        maxs[i+1] <== switchers[i+1].outL;
    }

    out <== maxs[n];
}
