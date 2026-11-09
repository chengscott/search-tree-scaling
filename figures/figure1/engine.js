/* Reproducible illustrative PUCT with batched virtual loss. No Atari inference. */
(function(global){
function hash(str){let h=2166136261;for(let i=0;i<str.length;i++){h^=str.charCodeAt(i);h=Math.imul(h,16777619)}return h>>>0}
function uniform(seed,key){return (hash(seed+':'+key)+.5)/4294967296}
function runTree(opts){const {c,budget,threads,seed,game,virtualLoss}=opts, actions=game==='freeway'?3:game==='pong'?6:6;const nodes=[];let batches=0;
function add(parent,action,prior,path){let id=nodes.length;nodes.push({id,parent,action,visits:0,virtual:0,total:0,p:prior,q:0,path,children:[],depth:parent<0?0:nodes[parent].depth+1});return id}
add(-1,-1,1,'root');
function expand(id){let n=nodes[id];if(n.children.length||n.depth>=32)return;let ws=Array.from({length:actions},(_,i)=>Math.pow(uniform(seed+game,n.path+'p'+i),3)+.01),sum=ws.reduce((a,b)=>a+b,0);ws.forEach((v,i)=>n.children.push(add(id,i,v/sum,n.path+'/'+i)))}
expand(0);
let done=0;while(done<budget){let pending=[];let batch=Math.min(threads,budget-done);for(let j=0;j<batch;j++){let path=[0],at=0;for(let depth=0;depth<32;depth++){let n=nodes[at];if(!n.children.length)break;let best=-Infinity,next=n.children[0],total=n.visits+n.virtual+1;for(let id of n.children){let child=nodes[id],v=child.visits+child.virtual;let q=v? (child.total-child.virtual)/(v): -1;let score=q+c*child.p*Math.sqrt(total)/(1+v);if(score>best){best=score;next=id}}at=next;path.push(at);if(!nodes[at].children.length)break}let leaf=nodes[at];if(virtualLoss)path.forEach(id=>nodes[id].virtual++);pending.push({path,at,value:.55+.28*Math.sin(leaf.depth*.45)+.16*(uniform(seed+game,leaf.path+'v')-.5)});}
for(let item of pending){expand(item.at);for(let id of item.path){let n=nodes[id];if(virtualLoss)n.virtual--;n.visits++;n.total+=item.value;n.q=n.total/n.visits}done++}batches++}
return {nodes:nodes.map(n=>[n.parent,n.action,n.visits,1,n.p,n.q]),batches,completed:done}}
global.Figure1Engine={runTree,hash};if(typeof module!=='undefined')module.exports=global.Figure1Engine;
})(typeof window!=='undefined'?window:globalThis);
