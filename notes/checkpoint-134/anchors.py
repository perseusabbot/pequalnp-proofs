"""Count the six-rectangle subsets excluded by symmetry from the radius-eight result."""
from collections import Counter
from itertools import combinations
from fractions import Fraction
import json
from math import comb

from verify import DATA, HERE, ROWS, SIZE, bits, require


def excluded_subgroups(generators, group):
    identity=bytes(range(42))
    tables=[(bytes.maketrans(identity, bytes(g)),bytes.maketrans(bytes(g),identity)) for g in generators]
    translate=lambda k:bytes([(i+k)%21 for i in range(21)] + [21+(i+k)%21 for i in range(21)])
    summary={}
    for prime, seed in [(3,translate(7)),(5,bytes(generators[1])),(7,translate(3))]:
        def canonical(permutation):
            table=bytes.maketrans(identity,permutation)
            power=identity.translate(table)
            powers=[]
            for _ in range(prime-1):
                powers.append(power)
                power=power.translate(table)
            require(power==identity and identity not in powers,'Expected prime-order generator')
            return min(powers)
        first=canonical(seed)
        queue=[first]
        seen={first}
        for h in queue:
            table=bytes.maketrans(identity,h)
            for g,inv in tables:
                conjugate=canonical(identity.translate(inv).translate(table).translate(g))
                if conjugate not in seen:
                    seen.add(conjugate)
                    queue.append(conjugate)
        all_elements=0
        for g in group:
            if g==identity:
                continue
            table=bytes.maketrans(identity,g)
            power=g
            for _ in range(prime-1):
                power=power.translate(table)
            if power==identity:
                all_elements+=1
        excluded=(prime-1)*len(seen)
        if prime in (5,7):
            require(excluded==all_elements,'Unexpected extra conjugacy class')
        summary[str(prime)]=dict(conjugate_subgroups=len(seen),excluded_elements=excluded,
                                 total_elements_of_order=all_elements)
    require(len(group)==2**8*3**3*5*7,'Unexpected group order')
    return summary


def classify():
    # Labels 0..20 are rows, 21..41 columns. A duality swaps the two sides.
    five = DATA['order_five']
    generators = [
        [(i+1)%21 for i in range(21)] + [21+(j+1)%21 for j in range(21)],
        five['row_permutation'] + [21+j for j in five['column_permutation']],
        [2*i%21 for i in range(21)] + [21+(2*j+7)%21 for j in range(21)],
        [21+(-i)%21 for i in range(21)] + [(-j)%21 for j in range(21)],
    ]
    for g in generators:
        require(sorted(g)==list(range(42)), 'Generator is not a permutation')
        for i in range(21):
            for j in range(21):
                x,y=sorted((g[i],g[j+21]))
                require(x<21<=y and ROWS[x]>>(y-21)&1 == ROWS[i]>>j&1, 'Generator changes board')
    tables=[bytes(g+list(range(42,256))) for g in generators]
    identity=bytes(range(42))
    group=[identity]
    seen={identity}
    for g in group:
        for table in tables:
            other=g.translate(table)
            if other not in seen:
                seen.add(other)
                group.append(other)

    example=json.loads((HERE.parent/'checkpoint-133'/'plane-examples.json').read_text())
    incumbent=[r | c<<SIZE for r,c in example['unrestricted']['rectangles']]
    index={w:i for i,w in enumerate(incumbent)}
    require(len(index)==14, 'Incumbent has a duplicate rectangle')
    sites=[tuple(bits(w)) for w in incumbent]
    powers=[1<<k for k in range(42)]
    subsets=[sum(1<<i for i in choice) for choice in combinations(range(14),6)]
    parent={s:s for s in subsets}
    stabilizer=Counter()
    overlap=Counter()
    domains=Counter()

    def root(s):
        while parent[s]!=s:
            parent[s]=parent[parent[s]]
            s=parent[s]
        return s

    for g in group:
        image={}
        for i,positions in enumerate(sites):
            dest=sum(powers[g[j]] for j in positions)
            if dest in index:
                image[i]=index[dest]
        overlap[len(image)]+=1
        if len(image)>=6:
            domains[sum(1<<i for i in image)]+=1
        for choice in combinations(image,6):
            source=sum(1<<i for i in choice)
            dest=sum(1<<image[i] for i in choice)
            if source==dest:
                stabilizer[source]+=1
            a,b=root(source),root(dest)
            parent[b]=a
    roots={root(s) for s in subsets}
    require(all(len(group)%stabilizer[s]==0 for s in roots), 'Bad orbit size')
    total=sum(len(group)//stabilizer[s] for s in roots)
    require(sum(overlap.values())==len(group) and len(subsets)==comb(14,6), 'Bad enumeration')
    # A second count needs only the domain of each partial permutation. If an
    # orbit meets the seed collection r times and has stabilizer h, precisely
    # r*h transformations send each of its seed subsets back into the seed.
    hit_counts=Counter(sum(count for mask,count in domains.items() if mask & s==s) for s in subsets)
    counted=sum(Fraction(len(group)*frequency, hits) for hits,frequency in hit_counts.items())
    require(counted==total, 'Incidence count disagrees with orbit/stabilizer count')
    return dict(group_size=len(group),incumbent_images=len(group)//overlap[14],
                incumbent_intersection_histogram=dict(sorted(overlap.items())),
                seed_subsets=len(subsets),subset_orbits=len(roots),
                orbit_stabilizers=dict(sorted(Counter(stabilizer[s] for s in roots).items())),
                seed_return_multiplicities=dict(sorted(hit_counts.items())),
                excluded_six_rectangle_subsets=total,
                excluded_prime_order_subgroups=excluded_subgroups(generators,group),
                full_cover_orbit_divisor=105)


if __name__ == '__main__':
    print(json.dumps(classify(),indent=2))
