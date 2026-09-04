# Independent check of the branchprobe n=5 hit.  Sets of worlds as frozensets.
W = [0,1,2,3,4]
RI = {0:{0,1,2,3,4}, 1:{1,2}, 2:{2}, 3:{3}, 4:{4}}
RM = {0:{0}, 1:{1,2}, 2:{2}, 3:{3}, 4:{4}}
F  = {2}
def IMP(A,B,W,RI): return frozenset(v for v in W if all((u not in A) or (u in B) for u in RI[v]))
def BOX(A,W,RI,RM,): return frozenset(v for v in W if all(any(y in A for y in RM[u]) for u in RI[v]))
def ev(f, vp, W, RI, RM, Fs):
    k=f[0]
    if k=='p': return vp
    if k=='b': return frozenset(Fs)
    if k=='&': return ev(f[1],vp,W,RI,RM,Fs)&ev(f[2],vp,W,RI,RM,Fs)
    if k=='|': return ev(f[1],vp,W,RI,RM,Fs)|ev(f[2],vp,W,RI,RM,Fs)
    if k=='>': return IMP(ev(f[1],vp,W,RI,RM,Fs),ev(f[2],vp,W,RI,RM,Fs),W,RI)
    if k=='O': return BOX(ev(f[1],vp,W,RI,RM,Fs),W,RI,RM)
B=('b',); P=('p',); OB=('O',B)
def N(x): return ('>',x,B)
# phi_club = ((p ⊃ ◯⊥) ∨ (¬p ⊃ ◯⊥)) ⊃ (¬◯⊥ ∨ (◯⊥ ∧ p))
PHI=('>',('|',('>',P,OB),('>',N(P),OB)),('|',N(OB),('&',OB,P)))
FULL=frozenset(W)
U=frozenset({1,2,3})
print("phi valid under U:", ev(PHI,U,W,RI,RM,F)==FULL)
# D(C): closure of {||bot||} under and,or,imp,box
D={frozenset(F)}
ch=True
while ch:
    ch=False
    for a in list(D):
        for b in list(D):
            for c in (a&b, a|b, IMP(a,b,W,RI)):
                if c not in D: D.add(c); ch=True
        c=BOX(a,W,RI,RM)
        if c not in D: D.add(c); ch=True
D=sorted(D,key=lambda s:sorted(s))
print("D(C):", [sorted(d) for d in D])
print("U undefinable:", U not in D)
print("all instances fail at 0:", all(0 not in ev(PHI,d,W,RI,RM,F) for d in D))
# the guarded 2-layer STRETCH: worlds (x,0) ground, (x,1) upper; inl x <= inr y iff x<=y and y in c
def stretch(c):
    W2=[(x,0) for x in W]+[(x,1) for x in W]
    RI2={}; RM2={}
    for x in W:
        RI2[(x,0)]={(y,0) for y in RI[x]} | {(y,1) for y in RI[x] if y in c}
        RI2[(x,1)]={(y,1) for y in RI[x]}
        RM2[(x,0)]={(y,0) for y in RM[x]}
        RM2[(x,1)]={(y,1) for y in RM[x]}
    F2={(x,0) for x in F}|{(x,1) for x in F}
    VP=frozenset({(x,1) for x in W} | {(x,0) for x in F})
    return W2,RI2,RM2,F2,VP
# the guarded FORK: cross edges out of x iff x not in c
def fork(c):
    W2=[(x,0) for x in W]+[(x,1) for x in W]
    RI2={}; RM2={}
    for x in W:
        cross0={(y,1) for y in RI[x]} if x not in c else set()
        cross1={(y,0) for y in RI[x]} if x not in c else set()
        RI2[(x,0)]={(y,0) for y in RI[x]} | cross0
        RI2[(x,1)]={(y,1) for y in RI[x]} | cross1
        RM2[(x,0)]={(y,0) for y in RM[x]}
        RM2[(x,1)]={(y,1) for y in RM[x]}
    F2={(x,0) for x in F}|{(x,1) for x in F}
    VP=frozenset({(x,0) for x in c} | {(x,1) for x in F})
    return W2,RI2,RM2,F2,VP
okS=okB=True
for d in D:
    for (name,mk) in (("stretch",stretch),("fork",fork)):
        W2,RI2,RM2,F2,VP=mk(d)
        val=ev(PHI,VP,W2,RI2,RM2,F2)
        if (0,0) in val:
            print("  !! phi HOLDS at ground copy of root in",name,"guard",sorted(d))
            if name=="stretch": okS=False
            else: okB=False
print("all guarded STRETCHES fail at root:", okS)
print("all guarded FORKS fail at root:", okB)
print("root not fallible:", 0 not in F)
