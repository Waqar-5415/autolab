import {parse,thompson,subset,minimize,elim,simulate,equiv,nfaOf,enumerate} from '../src/algorithms.js';
let pass=0,fail=0;const ok=(c,m)=>{c?pass++:(fail++,console.error('FAIL:',m))};
const build=src=>{const r=parse(src),ns=thompson(r.ast,r.alphabet),nfa=ns.at(-1).auto,sd=subset(nfa),mn=minimize(sd.dfa);return{r,nfa,dfa:sd.dfa,min:mn.min}};
// expected state counts from the proposal
let b=build('(a|b)*abb');ok(b.nfa.states.length===14,'NFA 14');ok(b.dfa.states.length===5,'DFA 5');ok(b.min.states.length===4,'min 4');
b=build('a*b*');ok(b.dfa.states.length===3,'a*b* DFA 3');ok(b.min.states.length===3&&b.min.states.filter(s=>s.meta.dead).length===1,'a*b* min 2+dead');
// language equivalence vs JS RegExp oracle (all strings up to length 8)
const strs=(al,n)=>{let out=[''],cur=[''];for(let i=0;i<n;i++){cur=cur.flatMap(s=>al.map(a=>s+a));out=out.concat(cur)}return out};
const cases=[['(a|b)*abb','ab'],['a*b*','ab'],['(ab|a)*b','ab'],['a+b?','ab'],['(a|)','ab'],['(0|1)*101','01'],['(a|b)*a(a|b)(a|b)','ab'],['((a|b)(a|b))*','ab'],['a?b?a?','ab'],['[a-c]+c*','abc'],['(a*b*)*','ab'],['(a|b)+','ab']];
for(const [src,al] of cases){const x=build(src),re=new RegExp('^(?:'+src.replace(/\(([^()]*)\|\)/g,'($1|)')+')$');
 for(const w of strs([...al],8)){const e=re.test(w);for(const [n,A] of [['nfa',x.nfa],['dfa',x.dfa],['min',x.min]])if(simulate(A,w).acc!==e){ok(false,`${src} ${n} on "${w}"`);break}}ok(true)}
// named accept/reject examples
const acc=(s,w)=>simulate(build(s).min,w).acc;
['abb','aabb','babb'].forEach(w=>ok(acc('(a|b)*abb',w),w));['ab','','abba'].forEach(w=>ok(!acc('(a|b)*abb',w),'rej '+w));
// round trip regex -> DFA -> regex' (state elimination) must be equivalent
for(const [src] of cases){const x=build(src),re=elim(x.dfa).regex;try{ok(equiv(x.nfa,nfaOf(re)).eq===true,`round-trip ${src} -> ${re}`)}catch(e){ok(false,`round-trip parse ${src} -> ${re}: ${e.message}`)}}
// parser errors
for(const bad of ['(a','a)','*a','a{2}','^a','\\1','[a','']){let t=false;try{parse(bad)}catch(e){t=e.pos!==undefined}ok(t,'parser rejects '+JSON.stringify(bad))}
ok(parse('a**').ast.t==='star','a**');ok(parse('((a))').ast.t==='lit','nested');
// equivalence + counter-example
ok(equiv(nfaOf('(a|b)*abb'),nfaOf('(a*b*)*abb')).eq===true,'equiv true');
const d=equiv(nfaOf('a*'),nfaOf('a+'));ok(d.eq===false&&d.w==='','shortest counter-example is empty string');
ok(enumerate(nfaOf('a+b?'),4).join()==='a,aa,ab,aaa','enumerate: '+enumerate(nfaOf('a+b?'),4).join());
console.log(`${pass} passed, ${fail} failed`);process.exit(fail?1:0);
