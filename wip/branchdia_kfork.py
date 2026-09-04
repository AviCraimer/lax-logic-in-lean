import os
exec(open(os.path.join(os.path.dirname(os.path.abspath(__file__)),'branchdia_verify.py')).read())
import itertools
# general k-fork: guard c, copies with p-valuations d_1..d_k, F <= d_i <= c,
# cross edges out of (x,i) exist iff x not in c.
def kfork(c, ds):
    k=len(ds)
    W2=[(x,i) for x in W for i in range(k)]
    RI2={}; RM2={}
    for x in W:
        for i in range(k):
            e={(y,i) for y in RI[x]}
            if x not in c:
                e |= {(y,j) for y in RI[x] for j in range(k)}
            RI2[(x,i)]=e
            RM2[(x,i)]={(y,i) for y in RM[x]}
    F2={(x,i) for x in F for i in range(k)}
    VP=frozenset({(x,i) for i in range(k) for x in ds[i]})
    return W2,RI2,RM2,F2,VP
Fs=frozenset(F)
hits={}
for k in (1,2,3,4):
    found=[]
    for c in D:
        cand=[d for d in D if Fs<=d<=c]
        for ds in itertools.product(cand, repeat=k):
            W2,RI2,RM2,F2,VP=kfork(c,ds)
            if (0,0) in ev(PHI,VP,W2,RI2,RM2,F2):
                found.append((sorted(c),[sorted(d) for d in ds]))
    hits[k]=found
    print(f"k={k}: {len(found)} k-forks force phi at the ground copy of the root",
          found[:3])
