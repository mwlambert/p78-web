/*! viewer-core.js — P78 cislunar mission viewer (simulation + renderer + loop).
 *
 *  Extracted from moon3.html so the viewer can run first-party in the page (no iframe).
 *  moon3.html stays the "studio" (controls + export) on top of this same core.
 *
 *  Usage (site / island):
 *    import { createViewer } from 'viewer-core';
 *    const v = createViewer(canvasEl, { interactive:false, P:{mode:'mission',...}, S:{...} });
 *    v.resize(w, h);      // call from a ResizeObserver, or pass {width,height} in config
 *    v.pause(); v.play(); v.destroy();
 *
 *  SSR-safe: NO window / document / location access at module top level — everything
 *  DOM-touching lives inside createViewer / resize / handlers. Safe to `import` under Node.
 */

export function createViewer(canvas, config) {
  config = config || {};
  function assign(base, over){ if(over) for(var kk in over){ if(Object.prototype.hasOwnProperty.call(over,kk)) base[kk]=over[kk]; } return base; }
  function nowMs(){ return (typeof performance!=='undefined' && performance.now) ? performance.now() : (+new Date()); }
  function raf(fn){ return (typeof requestAnimationFrame!=='undefined') ? requestAnimationFrame(fn) : setTimeout(function(){fn(nowMs());}, 16); }
  function caf(id){ if(id==null) return; if(typeof cancelAnimationFrame!=='undefined') cancelAnimationFrame(id); else clearTimeout(id); }
  function dprGet(){ return Math.min((typeof window!=='undefined' && window.devicePixelRatio) || 1, 2); }

  // ---------- constants ----------
  var DEG=Math.PI/180, DAY=86400, TWO=2*Math.PI;
  var muE=398600.4418, muM=4902.800, R_E=6371, R_M=1737.4;
  var aMoon=384400, eMoon=0.0549, iMoon=5.145*DEG, Tmoon=27.321661;   // Moon around Earth (days)
  var lagR=aMoon*Math.cbrt((muM/(muE+muM))/3);        // Earth–Moon L1/L2 distance from the Moon (~61,000 km)
  var STAGE_R=15000;                                   // schematic staging-orbit radius (support sat)
  var CAM_W=TWO/24000;

  // ---------- state (config-seeded) ----------
  var P = assign({mode:'orbit',primary:'moon',alt:100,e:0,inc:90,mag:22,span:8,raise:3,coast:1,periodMul:12,animDur:60,roundTrip:true,lloAlt:100,lloInc:90,showMoon:false,showSats:true,showLag:false,showTrail:true,showHop:true,showFleet:false,fleetDist:false,fleetTrail:false,sun:false}, config.P);
  var S = assign({sat:'#EAF1FF',moon:'#B9C2D0',earth:'#5C8CFF',ref:'#454b58',bg:'#000000',lw:1,glow:1,refop:0.55,tilt:49,drift:0}, config.S);
  var zoom = config.zoom!=null ? config.zoom : 1;
  var camYaw=0, panX=0, panY=0, camPhi=0;
  var cxFrac = config.cx!=null ? config.cx : 0.5;      // scene centre as a fraction of W/H (default 0.5 = middle).
  var cyFrac = config.cy!=null ? config.cy : 0.5;      // e.g. cy:0.7 drops the scene into the lower gap behind copy.
  var bscaleVal = config.bscale!=null ? config.bscale : 1;
  var interactive = config.interactive !== false;                       // default true; site backdrop passes false
  var wheelModifierOnly = !!config.wheelModifierOnly;                    // for interactive embeds inside a scrolling page
  var onCamera = typeof config.onCamera==='function' ? config.onCamera : null;
  var reduce = config.reducedMotion!=null ? config.reducedMotion
             : (typeof window!=='undefined' && window.matchMedia ? window.matchMedia('(prefers-reduced-motion: reduce)').matches : false);

  var traj={moon:[],sat:[],prim:[]}, satPeriod=0, satA=0, NOW=0;
  var bodyImg={sat:null,moon:null,earth:null}, bodyData={sat:null,moon:null,earth:null}, DIA={sat:26,moon:40,earth:56};
  // ═══ EDIT MARKER SIZES HERE ═══ radius in px (zoom-independent — they stay this size at any zoom).
  var MARK={depot:2, rocket:2, drone:2};   // depot = gold station · rocket = hopper · drone = the flying ship (kept ~rocket size)
  var texCache={earth:null,moon:null,ek:null,mk:null}, sgbuf={};
  var ctx = canvas.getContext('2d');
  var W=0, H=0, dpr=1;

  // ================= SIMULATION (verbatim from moon3.html) =================
  function keplerPos(a,e,inc,Om,w,nu){
    var p=a*(1-e*e)/(1+e*Math.cos(nu)),x=p*Math.cos(nu),y=p*Math.sin(nu),z=0,c,s,x1,y1,z1;
    c=Math.cos(w);s=Math.sin(w);x1=x*c-y*s;y1=x*s+y*c;x=x1;y=y1;
    c=Math.cos(inc);s=Math.sin(inc);y1=y*c-z*s;z1=y*s+z*c;y=y1;z=z1;
    c=Math.cos(Om);s=Math.sin(Om);x1=x*c-y*s;y1=x*s+y*c;x=x1;y=y1;
    return [x,y,z];
  }
  function trueAnom(M,e){M=((M%TWO)+TWO)%TWO;var E=M,k;for(k=0;k<6;k++)E=E-(E-e*Math.sin(E)-M)/(1-e*Math.cos(E));
    return 2*Math.atan2(Math.sqrt(1+e)*Math.sin(E/2),Math.sqrt(1-e)*Math.cos(E/2));}
  function periodDays(a,mu){return TWO*Math.sqrt(a*a*a/mu)/DAY;}

  function computeOrbit(){
    var prim=P.primary, R=(prim==='moon'?R_M:R_E), mu=(prim==='moon'?muM:muE);
    satA=R+P.alt; satPeriod=periodDays(satA,mu);
    var Tvis=satPeriod*P.periodMul;
    var N=8000, i,t,mp,pp,sr;
    traj.moon=[];traj.sat=[];traj.prim=[];
    for(i=0;i<=N;i++){
      t=P.span*i/N;
      mp=keplerPos(aMoon,eMoon,iMoon,0,0,trueAnom(TWO*t/Tmoon,eMoon));
      pp=(prim==='moon')?mp:[0,0,0];
      sr=keplerPos(satA,P.e,P.inc*DEG,0,0,trueAnom(TWO*t/Tvis,P.e));
      traj.moon.push(mp);traj.prim.push(pp);traj.sat.push([pp[0]+sr[0],pp[1]+sr[1],pp[2]+sr[2]]);
    }
  }
  function computeMission(){
    var r_leo=R_E+P.alt, incT=P.inc*DEG, Nr=Math.max(1,Math.round(P.raise));
    var target=aMoon*(1+eMoon), nLeo=2, nStage=2, kk, rap;
    var r_llo=R_M+P.lloAlt, incL=P.lloInc*DEG, lloMag=P.mag;
    var apoTgt=Math.max(r_leo*4, target-lloMag*r_llo), stageR=STAGE_R;
    function conic(a,e,nu){return keplerPos(a,e,incT,0,0,nu);}
    function elt(rp,ra){return {a:(rp+ra)/2,e:(ra-rp)/(ra+rp)};}
    var arcs=[{a:r_leo,e:0,M0:0,M1:TWO*nLeo,dur:nLeo*periodDays(r_leo,muE)}];
    var Eh=elt(r_leo,stageR); arcs.push({a:Eh.a,e:Eh.e,M0:0,M1:Math.PI,dur:0.5*periodDays(Eh.a,muE)});
    arcs.push({a:stageR,e:0,M0:Math.PI,M1:Math.PI+TWO*nStage+Math.PI,dur:(nStage+0.5)*periodDays(stageR,muE)});
    for(kk=1;kk<=Nr;kk++){rap=stageR*Math.pow(apoTgt/stageR,kk/(Nr+1));var Erk=elt(stageR,rap);
      arcs.push({a:Erk.a,e:Erk.e,M0:0,M1:TWO,dur:periodDays(Erk.a,muE)});}
    var Et=elt(stageR,apoTgt); arcs.push({a:Et.a,e:Et.e,M0:0,M1:Math.PI,dur:0.5*periodDays(Et.a,muE)});
    var sat=[],sumW=0,wk=[],j;
    for(kk=0;kk<arcs.length;kk++){wk[kk]=Math.sqrt(arcs[kk].dur);sumW+=wk[kk];}
    for(kk=0;kk<arcs.length;kk++){var ar=arcs[kk],st=Math.max(80,Math.round(2600*wk[kk]/sumW));
      for(j=0;j<st;j++)sat.push(conic(ar.a,ar.e,trueAnom(ar.M0+(ar.M1-ar.M0)*j/st,ar.e)));}
    sat.push(conic(Et.a,Et.e,Math.PI));
    var arrival=sat.length-1;
    var T_earth=0; for(kk=0;kk<arcs.length;kk++)T_earth+=arcs[kk].dur;
    var coast=Math.max(0.1,P.coast);
    var T_llo=periodDays(r_llo,muM), coils=Math.max(1,coast*Tmoon/(T_llo*P.periodMul));
    var earthSweep=TWO*T_earth/Tmoon, rate=earthSweep/arrival;
    var llo=Math.max(240,Math.min(16000,Math.round(coast*TWO/rate)));
    var startNu=Math.PI-earthSweep, moon=[],prim=[],all=[],i,nu,mp,lc,frac,gi;
    for(i=0;i<=arrival;i++){nu=startNu+rate*i;mp=keplerPos(aMoon,eMoon,iMoon,0,0,nu);moon.push(mp);prim.push([0,0,0]);all.push(sat[i]);}
    for(i=1;i<=llo;i++){gi=arrival+i;nu=startNu+rate*gi;frac=i/llo;mp=keplerPos(aMoon,eMoon,iMoon,0,0,nu);moon.push(mp);prim.push(mp);
      lc=keplerPos(r_llo,0,incL,0,0,TWO*coils*frac);all.push([mp[0]+lloMag*lc[0],mp[1]+lloMag*lc[1],mp[2]+lloMag*lc[2]]);}
    if(P.roundTrip){
      var exitPt=all[all.length-1];
      var apoR=Math.max(r_leo*4, Math.hypot(exitPt[0],exitPt[1],exitPt[2]));
      var vx=exitPt[0]/apoR, vy=exitPt[1]/apoR, vz=exitPt[2]/apoR;
      var ax=0, ay=vz, az=-vy, cA=-vx, sA=Math.hypot(ax,ay,az);
      var rot;
      if(sA<1e-9){ rot = cA>0 ? function(p){return [p[0],p[1],p[2]];} : function(p){return [-p[0],-p[1],p[2]];}; }
      else{ ax/=sA; ay/=sA; az/=sA;
        rot=function(p){var d=ax*p[0]+ay*p[1]+az*p[2];
          var kx=ay*p[2]-az*p[1], ky=az*p[0]-ax*p[2], kz=ax*p[1]-ay*p[0];
          return [p[0]*cA+kx*sA+ax*d*(1-cA), p[1]*cA+ky*sA+ay*d*(1-cA), p[2]*cA+kz*sA+az*d*(1-cA)];}; }
      var Er=elt(stageR,apoR), Ed=elt(r_leo,stageR), rarcs=[];
      rarcs.push({a:Er.a,e:Er.e,M0:Math.PI,M1:TWO,dur:0.5*periodDays(Er.a,muE)});
      for(kk=Nr;kk>=1;kk--){rap=stageR*Math.pow(apoTgt/stageR,kk/(Nr+1));var Elk=elt(stageR,rap);
        rarcs.push({a:Elk.a,e:Elk.e,M0:0,M1:TWO,dur:periodDays(Elk.a,muE)});}
      rarcs.push({a:stageR,e:0,M0:0,M1:TWO*nStage+Math.PI,dur:(nStage+0.5)*periodDays(stageR,muE)});
      rarcs.push({a:Ed.a,e:Ed.e,M0:Math.PI,M1:TWO,dur:0.5*periodDays(Ed.a,muE)});
      rarcs.push({a:r_leo,e:0,M0:0,M1:TWO*nLeo,dur:nLeo*periodDays(r_leo,muE)});
      var sumR=0,wr=[],gidx=arrival+llo,j2,pR;
      for(kk=0;kk<rarcs.length;kk++){wr[kk]=Math.sqrt(rarcs[kk].dur);sumR+=wr[kk];}
      for(kk=0;kk<rarcs.length;kk++){var rc=rarcs[kk],stR=Math.max(80,Math.round(2600*wr[kk]/sumR));
        for(j2=0;j2<stR;j2++){pR=rot(conic(rc.a,rc.e,trueAnom(rc.M0+(rc.M1-rc.M0)*j2/stR,rc.e)));
          gidx++;nu=startNu+rate*gidx;mp=keplerPos(aMoon,eMoon,iMoon,0,0,nu);moon.push(mp);prim.push([0,0,0]);all.push(pR);}}
      var lastIdx=moon.length-1, curSweep=rate*lastIdx;
      traj.missionOrbits=curSweep/TWO;
      var padN=Math.round((Math.ceil(curSweep/TWO-1e-6)*TWO-curSweep)/rate);
      var hold=all[all.length-1];
      for(i=1;i<=padN;i++){gi=lastIdx+i;nu=startNu+rate*gi;mp=keplerPos(aMoon,eMoon,iMoon,0,0,nu);
        moon.push(mp);prim.push([0,0,0]);all.push(hold);}
    }
    traj.moon=moon;traj.prim=prim;traj.sat=all;
    traj.loopOrbits=rate>0?rate*(moon.length-1)/TWO:0;
    if(!P.roundTrip)traj.missionOrbits=traj.loopOrbits;
    traj.spd=rate>0?(TWO/Tmoon)/rate:80;
    traj.rate=rate;
    var cum=[0],ci,_dx,_dy,_dz;
    for(ci=1;ci<all.length;ci++){_dx=all[ci][0]-all[ci-1][0];_dy=all[ci][1]-all[ci-1][1];_dz=all[ci][2]-all[ci-1][2];cum[ci]=cum[ci-1]+Math.sqrt(_dx*_dx+_dy*_dy+_dz*_dz);}
    traj.cum=cum;
  }
  function computeFraming(){
    var n=traj.sat.length,i,cx=0,cy=0,cz=0,acc=[];
    for(i=0;i<n;i++)acc.push(satPlot(i));
    for(i=0;i<traj.moon.length;i++)acc.push(traj.moon[i]);
    acc.push([0,0,0]);
    n=acc.length;
    for(i=0;i<n;i++){cx+=acc[i][0];cy+=acc[i][1];cz+=acc[i][2];}
    cx/=n;cy/=n;cz/=n;
    var rm=1,dx,dy,dz,d;
    for(i=0;i<n;i++){dx=acc[i][0]-cx;dy=acc[i][1]-cy;dz=acc[i][2]-cz;d=Math.sqrt(dx*dx+dy*dy+dz*dz);if(d>rm)rm=d;}
    traj.C=[cx,cy,cz];traj.rMax=rm;
  }
  function compute(){if(P.mode==='mission')computeMission();else computeOrbit();computeFraming();}
  function lastHead(){return traj.sat.length-1;}

  // ================= PROJECTION / STYLE =================
  function hexRGB(h){h=(h||'#000000').replace('#','');if(h.length===3)h=h[0]+h[0]+h[1]+h[1]+h[2]+h[2];
    return parseInt(h.slice(0,2),16)+','+parseInt(h.slice(2,4),16)+','+parseInt(h.slice(4,6),16);}
  function projector(W,H,phi){
    var tl=S.tilt*DEG,ct=Math.cos(tl),st=Math.sin(tl),cph=Math.cos(phi),sph=Math.sin(phi);
    var C=traj.C||[0,0,0], rMax=traj.rMax||aMoon;
    var SC=Math.min(W,H)*0.5/(rMax*1.14)*zoom, cx=W*cxFrac+panX, cy=H*cyFrac+panY;
    return function(pt){var X=pt[0]-C[0],Y=pt[1]-C[1],Z=pt[2]-C[2];
      var x=X*cph-Y*sph,y=X*sph+Y*cph,z=Z,yv=y*ct-z*st,zv=y*st+z*ct;return [cx+x*SC,cy-yv*SC,zv];};
  }
  function satPlot(i){if(P.mode==='mission')return traj.sat[i];var s=traj.sat[i],p=traj.prim[i],m=P.mag;return [p[0]+m*(s[0]-p[0]),p[1]+m*(s[1]-p[1]),p[2]+m*(s[2]-p[2])];}

  // ================= BODY ART =================
  function bscale(){ return bscaleVal; }
  function skf(W,H){return Math.max(0.6,Math.min(W,H)/760);}
  function dot(c,x,y,r,hex,blur){c.fillStyle=hex;c.shadowColor=hex;c.shadowBlur=blur;c.beginPath();c.arc(x,y,r,0,7);c.fill();c.shadowBlur=0;}
  function twinkleDot(c,x,y,r,core,body,blur){if(blur>0){c.save();c.shadowColor=body;c.shadowBlur=blur;c.fillStyle=body;c.beginPath();c.arc(x,y,r*0.9,0,7);c.fill();c.restore();}
    var g=c.createRadialGradient(x-r*0.32,y-r*0.36,r*0.08,x,y,r);g.addColorStop(0,core);g.addColorStop(0.55,body);g.addColorStop(1,body);
    c.fillStyle=g;c.beginPath();c.arc(x,y,r,0,7);c.fill();}
  function mulberry(a){return function(){a|=0;a=a+0x6D2B79F5|0;var t=Math.imul(a^a>>>15,1|a);t=t+Math.imul(t^t>>>7,61|t)^t;return((t^t>>>14)>>>0)/4294967296;};}
  function hexArr(h){h=(h||'#888888').replace('#','');if(h.length===3)h=h[0]+h[0]+h[1]+h[1]+h[2]+h[2];return[parseInt(h.slice(0,2),16),parseInt(h.slice(2,4),16),parseInt(h.slice(4,6),16)];}
  function cl255(v){return v<0?0:v>255?255:v|0;}
  function shade(a,f){return f>=0?[cl255(a[0]+(255-a[0])*f),cl255(a[1]+(255-a[1])*f),cl255(a[2]+(255-a[2])*f)]:[cl255(a[0]*(1+f)),cl255(a[1]*(1+f)),cl255(a[2]*(1+f))];}
  function rgbs(a){return'rgb('+a[0]+','+a[1]+','+a[2]+')';}
  function rgba(a,al){return'rgba('+a[0]+','+a[1]+','+a[2]+','+al+')';}
  function newTex(){var cv=document.createElement('canvas');cv.width=512;cv.height=256;return cv;}
  function wrapEll(g,cx,cy,rx,ry,fill,W){for(var d=-1;d<=1;d++){g.save();g.translate(cx+d*W,cy);g.beginPath();g.ellipse(0,0,rx,ry,0,0,7);g.fillStyle=fill;g.fill();g.restore();}}
  function buildEarthTex(base){var cv=newTex(),W=cv.width,H=cv.height,g=cv.getContext('2d'),b=hexArr(base);
    var og=g.createLinearGradient(0,0,0,H);og.addColorStop(0,rgbs(shade(b,-0.35)));og.addColorStop(0.5,rgbs(shade(b,0.06)));og.addColorStop(1,rgbs(shade(b,-0.4)));
    g.fillStyle=og;g.fillRect(0,0,W,H);
    var rnd=mulberry(1337),land=[63,125,58],land2=[92,154,74],coast=[183,160,97],i,j,blobs=[];
    for(i=0;i<7;i++){var ccx=rnd()*W,ccy=40+rnd()*(H-80),parts=3+((rnd()*4)|0),spread=22+rnd()*42;
      for(j=0;j<parts;j++){var ox=(rnd()-0.5)*spread*2,oy=(rnd()-0.5)*spread,rx=15+rnd()*30,ry=10+rnd()*20,r2=rnd();
        wrapEll(g,ccx+ox,ccy+oy,rx,ry,rgbs(r2<0.28?coast:(r2<0.62?land2:land)),W);
        if(r2>=0.28)blobs.push([ccx+ox,ccy+oy,rx*0.8,ry*0.8]);}}
    var top=g.createLinearGradient(0,0,0,H*0.15);top.addColorStop(0,'rgba(255,255,255,0.95)');top.addColorStop(1,'rgba(255,255,255,0)');g.fillStyle=top;g.fillRect(0,0,W,H*0.15);
    var bot=g.createLinearGradient(0,H,0,H*0.85);bot.addColorStop(0,'rgba(255,255,255,0.95)');bot.addColorStop(1,'rgba(255,255,255,0)');g.fillStyle=bot;g.fillRect(0,H*0.85,W,H*0.15);
    for(i=0;i<15;i++){var clx=rnd()*W,cly=rnd()*H,cw=20+rnd()*60,ch=6+rnd()*13,a=(0.10+rnd()*0.20).toFixed(3);wrapEll(g,clx,cly,cw,ch,'rgba(255,255,255,'+a+')',W);}
    var lc=newTex(),lg=lc.getContext('2d');
    for(i=0;i<blobs.length;i++){var B=blobs[i],n=26+((rnd()*34)|0);
      for(j=0;j<n;j++){var a2=rnd()*6.28,rr=Math.sqrt(rnd()),lx=B[0]+Math.cos(a2)*B[2]*rr,ly=B[1]+Math.sin(a2)*B[3]*rr,al=(0.6+rnd()*0.4).toFixed(2);
        for(var dd=-1;dd<=1;dd++){lg.beginPath();lg.arc(lx+dd*W,ly,rnd()*0.6+0.4,0,7);lg.fillStyle='rgba(255,216,150,'+al+')';lg.fill();}}}
    return {cv:cv,lights:lc};}
  function buildMoonTex(base){var cv=newTex(),W=cv.width,H=cv.height,g=cv.getContext('2d'),b=hexArr(base);
    var og=g.createLinearGradient(0,0,0,H);og.addColorStop(0,rgbs(shade(b,-0.18)));og.addColorStop(0.5,rgbs(shade(b,0.07)));og.addColorStop(1,rgbs(shade(b,-0.2)));
    g.fillStyle=og;g.fillRect(0,0,W,H);
    var rnd=mulberry(9021),i,d;
    for(i=0;i<6;i++){var mx=rnd()*W,my=30+rnd()*(H-60),rx=26+rnd()*44,ry=18+rnd()*28;wrapEll(g,mx,my,rx,ry,rgba(shade(b,-0.3),0.5),W);}
    for(i=0;i<44;i++){var cx=rnd()*W,cy=rnd()*H,r=2+rnd()*8;for(d=-1;d<=1;d++){var px=cx+d*W;
      g.beginPath();g.arc(px,cy,r,0,7);g.fillStyle=rgbs(shade(b,0.12));g.fill();
      g.beginPath();g.arc(px,cy,r*0.78,0,7);g.fillStyle=rgbs(shade(b,-0.16));g.fill();
      g.beginPath();g.arc(px-r*0.18,cy-r*0.18,r*0.5,0,7);g.fillStyle=rgbs(shade(b,0.05));g.fill();}}
    return {cv:cv,lights:null};}
  function texData(cv){return cv.getContext('2d').getImageData(0,0,cv.width,cv.height);}
  function SGBUF(d){var b=sgbuf[d];if(!b){var cv=document.createElement('canvas');cv.width=d;cv.height=d;b={cv:cv,ctx:cv.getContext('2d')};sgbuf[d]=b;}return b;}
  function earthTex(){if(texCache.ek!==S.earth){var t=buildEarthTex(S.earth);texCache.earth={day:texData(t.cv),lights:texData(t.lights)};texCache.ek=S.earth;}return texCache.earth;}
  function moonTex(){if(texCache.mk!==S.moon){var t=buildMoonTex(S.moon);texCache.moon={day:texData(t.cv),lights:null};texCache.mk=S.moon;}return texCache.moon;}
  function shadedGlobe(c,x,y,R,dayD,lightsD,rot,sCam,ambient,flat){
    var d=Math.max(4,Math.ceil(2*R)),buf=SGBUF(d),bx=buf.ctx,img=bx.createImageData(d,d),data=img.data;
    var tw=dayD.width,th=dayD.height,td=dayD.data,ld=lightsD?lightsD.data:null;
    var frac=((rot%1)+1)%1,sr=sCam[0],su=sCam[1],sv=sCam[2],px,py,o;
    for(py=0;py<d;py++){var nyd=(py+0.5-R)/R;
      for(px=0;px<d;px++){var nx=(px+0.5-R)/R,r2=nx*nx+nyd*nyd;o=(py*d+px)*4;
        if(r2>1){data[o+3]=0;continue;}
        var u=((px/d)+frac)%1;if(u<0)u+=1;var v=nyd*0.5+0.5;
        var tx=(u*tw)|0,ty=(v*th)|0;if(ty<0)ty=0;if(ty>=th)ty=th-1;if(tx>=tw)tx=tw-1;var to=(ty*tw+tx)*4;
        var br,tf;
        if(flat){br=1-0.32*r2;}
        else{var nz=Math.sqrt(1-r2),lam=nx*sr+(-nyd)*su+nz*sv;tf=lam+0.14;tf=tf<0?0:tf>0.28?1:tf/0.28;br=ambient+(1-ambient)*tf;}
        data[o]=td[to]*br;data[o+1]=td[to+1]*br;data[o+2]=td[to+2]*br;data[o+3]=255;
        if(ld&&!flat){var la=ld[to+3];if(la>0){var ad=(la/255)*(0.45+0.55*(1-tf));
          data[o]=cl255(data[o]+ld[to]*ad);data[o+1]=cl255(data[o+1]+ld[to+1]*ad);data[o+2]=cl255(data[o+2]+ld[to+2]*ad);}}
      }}
    bx.putImageData(img,0,0);
    c.save();c.beginPath();c.arc(x,y,R,0,7);c.clip();c.drawImage(buf.cv,x-R,y-R);c.restore();}
  function drawGlobe(c,x,y,R,day,lights,rot,isEarth,hex,blur,sCam,flat){
    shadedGlobe(c,x,y,R,day,lights,rot,sCam,isEarth?0.05:0.015,flat);}
  var SUNW=(function(){var v=[0.68,-0.42,0.60],m=Math.hypot(v[0],v[1],v[2]);return[v[0]/m,v[1]/m,v[2]/m];})();
  function sunCam(phi){var tl=S.tilt*DEG,ct=Math.cos(tl),st=Math.sin(tl),cph=Math.cos(phi),sph=Math.sin(phi);
    var rx=SUNW[0]*cph-SUNW[1]*sph,y1=SUNW[0]*sph+SUNW[1]*cph;
    return [rx, y1*ct-SUNW[2]*st, y1*st+SUNW[2]*ct];}
  function bodyOrDot(c,x,y,which,dotR,hex,blur,k,lit,sCam){var im=bodyImg[which];
    if(im&&im.complete&&im.naturalWidth){var d=DIA[which]*k*bscale();c.drawImage(im,x-d/2,y-d/2,d,d);return;}
    if(which==='earth'||which==='moon'){var T=which==='earth'?earthTex():moonTex();
      drawGlobe(c,x,y,dotR,T.day,T.lights,NOW*(which==='earth'?0.0000038:0.0000016),which==='earth',hex,blur,sCam||[-0.6,0.5,0.6],!P.sun);return;}
    if(lit){
      if(blur>0){c.save();c.shadowColor=hex;c.shadowBlur=blur;c.fillStyle=hex;c.beginPath();c.arc(x,y,dotR*0.85,0,7);c.fill();c.restore();}
      var g=c.createRadialGradient(x-dotR*0.42,y-dotR*0.5,dotR*0.12,x,y,dotR*1.04);
      g.addColorStop(0,lit);g.addColorStop(0.55,hex);g.addColorStop(1,'#06080e');
      c.fillStyle=g;c.beginPath();c.arc(x,y,dotR,0,7);c.fill();return;}
    dot(c,x,y,dotR,hex,blur);}
  function drawLag(c,p,label,k){var r=3.6*k;c.strokeStyle='rgba(255,150,90,0.8)';c.lineWidth=Math.max(1,1*k);
    c.beginPath();c.moveTo(p[0]-r,p[1]);c.lineTo(p[0]+r,p[1]);c.moveTo(p[0],p[1]-r);c.lineTo(p[0],p[1]+r);c.stroke();
    c.fillStyle='rgba(255,170,110,0.9)';c.font=Math.round(9.5*k)+'px ui-monospace, Menlo, monospace';c.textAlign='left';c.textBaseline='middle';
    c.fillText(label,p[0]+r+3,p[1]);}
  function drawLaunch(c,pr,bp,ring,inc,dPhase,dRate,seed,k){
    var cyc=((NOW*0.00009+seed)%1+1)%1; if(cyc>0.82)return;
    var t=Math.min(1,cyc/0.40);
    var dAng=dPhase+dRate*NOW;
    var ud=keplerPos(1,0,inc,0,0,dAng);
    var th=keplerPos(1,0,inc,0,0,dAng+Math.PI/2);
    var ul=keplerPos(1,0,inc,0,0,dAng-0.9), rS=ring*0.11;
    var O =[bp[0]+ring*ud[0],bp[1]+ring*ud[1],bp[2]+ring*ud[2]];
    var P0=[bp[0]+rS*ul[0],bp[1]+rS*ul[1],bp[2]+rS*ul[2]];
    var P1=[bp[0]+ring*0.5*ul[0],bp[1]+ring*0.5*ul[1],bp[2]+ring*0.5*ul[2]];
    var P2=[O[0]-ring*0.5*th[0],O[1]-ring*0.5*th[1],O[2]-ring*0.5*th[2]];
    function bez(u){var m=1-u,a=m*m*m,b=3*m*m*u,d=3*m*u*u,e=u*u*u;
      return [a*P0[0]+b*P1[0]+d*P2[0]+e*O[0],a*P0[1]+b*P1[1]+d*P2[1]+e*O[1],a*P0[2]+b*P1[2]+d*P2[2]+e*O[2]];}
    var p=pr(bez(t));dot(c,p[0],p[1],MARK.rocket*k,'#ffd0a0',MARK.rocket*1.4*k*S.glow);}   // rocket size = MARK.rocket (k here is the constant kl passed in)
  function fillBg(c,W,H){c.fillStyle=S.bg;c.fillRect(0,0,W,H);}
  function bgDepth(c,W,H){var g=c.createRadialGradient(W/2,H*0.46,0,W/2,H*0.46,Math.max(W,H)*0.62);
    g.addColorStop(0,'rgba(30,42,70,0.22)');g.addColorStop(0.5,'rgba(14,20,36,0.12)');g.addColorStop(1,'rgba(0,0,0,0)');
    c.fillStyle=g;c.fillRect(0,0,W,H);}
  var MWBN=(function(){var v=[0.32,0.44,0.84],m=Math.hypot(v[0],v[1],v[2]);return[v[0]/m,v[1]/m,v[2]/m];})();
  var STARS=(function(){var a=[],seed=20240718,rnd=function(){seed=(seed*1103515245+12345)&0x7fffffff;return seed/0x7fffffff;},i,u,th,r,bn=MWBN;
    for(i=0;i<1200;i++){u=rnd()*2-1;th=rnd()*TWO;r=Math.sqrt(1-u*u);
      a.push([r*Math.cos(th),r*Math.sin(th),u,rnd()*0.9+0.4,rnd()*0.5+0.18]);}
    for(i=0;i<5200;i++){u=rnd()*2-1;th=rnd()*TWO;r=Math.sqrt(1-u*u);var dx=r*Math.cos(th),dy=r*Math.sin(th),dz=u;
      var dd=Math.abs(dx*bn[0]+dy*bn[1]+dz*bn[2]);if(dd>0.19)continue;
      a.push([dx,dy,dz,rnd()*0.55+0.28,(rnd()*0.24+0.09)*(1-dd/0.19)]);}
    for(i=0;i<18;i++){u=rnd()*2-1;th=rnd()*TWO;r=Math.sqrt(1-u*u);
      a.push([r*Math.cos(th),r*Math.sin(th),u,rnd()*1.1+1.3,rnd()*0.25+0.55]);}
    return a;})();
  var MWNEB=(function(){var a=[],seed=99177,rnd=function(){seed=(seed*1103515245+12345)&0x7fffffff;return seed/0x7fffffff;},i,u,th,r,bn=MWBN;
    for(i=0;i<130;i++){u=rnd()*2-1;th=rnd()*TWO;r=Math.sqrt(1-u*u);var dx=r*Math.cos(th),dy=r*Math.sin(th),dz=u;
      var dd=Math.abs(dx*bn[0]+dy*bn[1]+dz*bn[2]);if(dd>0.11)continue;
      a.push([dx,dy,dz,rnd()*0.09+0.05,(rnd()*0.05+0.03)*(1-dd/0.11)]);}
    return a;})();
  function drawStars(c,W,H,phi){
    var tl=S.tilt*DEG,ct=Math.cos(tl),st=Math.sin(tl),cph=Math.cos(phi),sph=Math.sin(phi);
    var cx=W/2,cy=H/2,R=0.56*Math.hypot(W,H),rr=Math.max(0.4,Math.min(W,H)/1100),mwr=Math.min(W,H),i,s,x,y,z,yv,zv;
    c.save();c.globalCompositeOperation='lighter';
    for(i=0;i<MWNEB.length;i++){s=MWNEB[i];
      x=s[0]*cph-s[1]*sph; y=s[0]*sph+s[1]*cph; z=s[2];
      yv=y*ct-z*st; zv=y*st+z*ct; if(zv<-0.15)continue;
      var nx=cx+x*R,ny=cy-yv*R,nrad=s[3]*mwr,na=s[4]*Math.min(1,0.4+zv);
      var ng=c.createRadialGradient(nx,ny,0,nx,ny,nrad);
      ng.addColorStop(0,'rgba(170,182,220,'+na.toFixed(3)+')');ng.addColorStop(1,'rgba(170,182,220,0)');
      c.fillStyle=ng;c.beginPath();c.arc(nx,ny,nrad,0,7);c.fill();}
    c.restore();
    c.fillStyle='#c9d3e6';
    for(i=0;i<STARS.length;i++){s=STARS[i];
      x=s[0]*cph-s[1]*sph; y=s[0]*sph+s[1]*cph; z=s[2];
      yv=y*ct-z*st; zv=y*st+z*ct;
      if(zv<0)continue;
      c.globalAlpha=s[4]*Math.min(1,0.3+zv);
      c.beginPath();c.arc(cx+x*R,cy-yv*R,s[3]*rr,0,7);c.fill();}
    c.globalAlpha=1;}
  var AMBS=[{body:0,phase:1.1,rate:0.00060},{body:1,phase:2.4,rate:0.00095}];
  function arcIndex(L,cum,hi){var lo=0,h=hi,m;while(lo<h){m=(lo+h)>>1;if(cum[m]<L)lo=m+1;else h=m;}return lo;}
  function trailPaint(c,pts,head,total,rgb,k,full,occ,env,grow){env=env==null?1:env;c.lineWidth=0.85*k*S.lw;c.lineJoin='round';c.lineCap='round';var i,al,cur,prev;
    if(full){for(i=1;i<=total;i++){if(occ&&(occ(pts[i])||occ(pts[i-1])))continue;c.strokeStyle='rgba('+rgb+',0.5)';c.beginPath();c.moveTo(pts[i-1][0],pts[i-1][1]);c.lineTo(pts[i][0],pts[i][1]);c.stroke();}return;}
    if(grow){var lead=Math.max(1,total*0.16);
      for(i=1;i<=head;i++){if(occ&&(occ(pts[i])||occ(pts[i-1])))continue;
        al=(0.30+0.55*Math.max(0,1-(head-i)/lead))*env;c.strokeStyle='rgba('+rgb+','+al.toFixed(3)+')';
        c.beginPath();c.moveTo(pts[i-1][0],pts[i-1][1]);c.lineTo(pts[i][0],pts[i][1]);c.stroke();}return;}
    var TAIL=Math.max(40,Math.round(total*0.62)),j;
    for(j=0;j<TAIL;j++){cur=((head-j)%total+total)%total;prev=((head-j-1)%total+total)%total;
      if(Math.abs(cur-prev)!==1)continue;
      if(occ&&(occ(pts[cur])||occ(pts[prev])))continue;
      al=(1-j/TAIL);al=al*al*0.92*env;if(al<0.012)continue;
      c.strokeStyle='rgba('+rgb+','+al.toFixed(3)+')';c.beginPath();c.moveTo(pts[prev][0],pts[prev][1]);c.lineTo(pts[cur][0],pts[cur][1]);c.stroke();}
    c.save();c.globalCompositeOperation='lighter';var HOT=Math.min(TAIL,14),hw;
    for(j=0;j<HOT;j++){cur=((head-j)%total+total)%total;prev=((head-j-1)%total+total)%total;
      if(Math.abs(cur-prev)!==1)continue;if(occ&&(occ(pts[cur])||occ(pts[prev])))continue;
      hw=(1-j/HOT);hw=hw*hw*0.5*env;if(hw<0.01)continue;
      c.strokeStyle='rgba(235,242,255,'+hw.toFixed(3)+')';c.lineWidth=0.85*k*S.lw*(1+0.5*(1-j/HOT));
      c.beginPath();c.moveTo(pts[prev][0],pts[prev][1]);c.lineTo(pts[cur][0],pts[cur][1]);c.stroke();}
    c.restore();}

  // ================= PAINT =================
  function paint(c,W,H,head,phi,o){
    o=o||{};var k=skf(W,H)*zoom,kl=skf(W,H),total=lastHead();if(!o.transparent){fillBg(c,W,H);bgDepth(c,W,H);drawStars(c,W,H,phi);}   // k = mark scale (scales with zoom); kl = stroke scale (constant, no zoom) so lines don't thicken when zooming
    var pr=projector(W,H,phi),sCam=sunCam(phi),i,e;
    if(P.showMoon){c.strokeStyle='rgba('+hexRGB(S.ref)+','+S.refop+')';c.lineWidth=1*kl;c.beginPath();
      for(i=0;i<=total;i++){e=pr(traj.moon[i]);if(i===0)c.moveTo(e[0],e[1]);else c.lineTo(e[0],e[1]);}c.stroke();}
    var eP=pr([0,0,0]), mP=pr(traj.moon[head]);
    var SCbody=Math.min(W,H)*0.5/((traj.rMax||aMoon)*1.14)*zoom;                     // projector's linear scale (px per sim-unit)
    var eR=(P.mode==='mission')?Math.max(3,R_E*SCbody):6.5*k, mR=4*k;                // mission: draw Earth at its TRUE radius so LEO/staging sit above the surface (not swallowed by the icon); orbit-mode keeps the visible icon
    function occ(p){var dx=p[0]-eP[0],dy=p[1]-eP[1];
      if(dx*dx+dy*dy<eR*eR*0.82 && p[2]<eP[2])return true;
      dx=p[0]-mP[0];dy=p[1]-mP[1];return (dx*dx+dy*dy<mR*mR*0.82 && p[2]<mP[2]);}
    bodyOrDot(c,eP[0],eP[1],'earth',eR,S.earth,16*k*S.glow,k,'#b7ccff',sCam);
    var spts=[];for(i=0;i<=total;i++)spts.push(pr(satPlot(i)));
    if(P.showTrail)trailPaint(c,spts,head,total,hexRGB(S.sat),kl,o.full,occ,o.env,o.grow);   // kl → constant trail thickness
    bodyOrDot(c,mP[0],mP[1],'moon',mR,S.moon,8*k*S.glow,k,'#eef2f8',sCam);
    if(P.showSats){var j,A,bp,rad,inc,ang,uu,asp;for(j=0;j<AMBS.length;j++){A=AMBS[j];
      if(A.body===0){bp=[0,0,0];rad=STAGE_R;inc=P.inc*DEG;}
      else{bp=traj.moon[head];rad=P.mag*(R_M+(P.mode==='mission'?P.lloAlt:P.alt));inc=(P.mode==='mission'?P.lloInc:P.inc)*DEG;}
      ang=A.phase+A.rate*NOW;uu=keplerPos(rad,0,inc,0,0,ang);
      asp=pr([bp[0]+uu[0],bp[1]+uu[1],bp[2]+uu[2]]);if(occ(asp))continue;twinkleDot(c,asp[0],asp[1],MARK.depot*kl,'#fff2cf','#e6bf5c',MARK.depot*0.7*kl*S.glow);}}   // depot size = MARK.depot (constant kl scale)
    if(P.showFleet && P.mode==='mission'){var fd,foff,fa,ca,sa,fidx,fq,fp,rt=traj.rate||0,
        mfrac=(traj.missionOrbits&&traj.loopOrbits)?traj.missionOrbits/traj.loopOrbits:1,mSamp=Math.round(total*mfrac),NF=12,
        cum=traj.cum,Lm=(P.fleetDist&&cum)?cum[Math.min(cum.length-1,mSamp)]:0,
        srgb=hexRGB(S.sat),TL=Math.max(40,Math.round(total*0.4)),jj,ci2,pi2,qb,pb2,pa2,al2;
      for(fd=1;fd<=NF;fd++){
        if(P.fleetDist&&cum&&Lm>0){foff=arcIndex(fd/(NF+1)*Lm,cum,mSamp);}
        else{foff=Math.round(fd/(NF+1)*mSamp);}
        fa=rt*foff;ca=Math.cos(fa);sa=Math.sin(fa);
        fidx=((head-foff)%total+total)%total;
        if(P.fleetTrail){c.lineWidth=1*kl;pa2=null;pi2=-9;
          for(jj=0;jj<TL;jj+=2){ci2=((fidx-jj)%total+total)%total;
            qb=satPlot(ci2);pb2=pr([qb[0]*ca-qb[1]*sa, qb[0]*sa+qb[1]*ca, qb[2]]);
            if(pa2&&Math.abs(ci2-pi2)<=3){al2=(1-jj/TL);al2=al2*al2*0.5;
              c.strokeStyle='rgba('+srgb+','+al2.toFixed(3)+')';c.beginPath();c.moveTo(pa2[0],pa2[1]);c.lineTo(pb2[0],pb2[1]);c.stroke();}
            pa2=pb2;pi2=ci2;}}
        fq=satPlot(fidx);fp=pr([fq[0]*ca-fq[1]*sa, fq[0]*sa+fq[1]*ca, fq[2]]);
        if(occ(fp))continue;bodyOrDot(c,fp[0],fp[1],'sat',MARK.drone*kl,S.sat,MARK.drone*2*kl*S.glow,kl);}}   // escorts = same size as the main drone (MARK.drone)
    if(P.showHop){
      drawLaunch(c,pr,traj.moon[head], P.mag*(R_M+(P.mode==='mission'?P.lloAlt:P.alt)), (P.mode==='mission'?P.lloInc:P.inc)*DEG, AMBS[1].phase, AMBS[1].rate, 0.20, kl);
      drawLaunch(c,pr,[0,0,0], STAGE_R, P.inc*DEG, AMBS[0].phase, AMBS[0].rate, 0.66, kl);}   // kl → rockets stay small dots at any zoom
    if(P.showLag){var mw=traj.moon[head],md=Math.hypot(mw[0],mw[1],mw[2])||1,ux=mw[0]/md,uy=mw[1]/md,uz=mw[2]/md;
      drawLag(c,pr([mw[0]-lagR*ux,mw[1]-lagR*uy,mw[2]-lagR*uz]),'L1',k);
      drawLag(c,pr([mw[0]+lagR*ux,mw[1]+lagR*uy,mw[2]+lagR*uz]),'L2',k);}
    var sh=spts[head];c.save();c.globalAlpha=(o.env==null?1:o.env);
    var db=MARK.drone*2.3*kl;   // drone-head bloom radius (constant kl scale)
    c.globalCompositeOperation='lighter';var hg=c.createRadialGradient(sh[0],sh[1],0,sh[0],sh[1],db);
    hg.addColorStop(0,'rgba('+hexRGB(S.sat)+',0.55)');hg.addColorStop(0.5,'rgba('+hexRGB(S.sat)+',0.14)');hg.addColorStop(1,'rgba('+hexRGB(S.sat)+',0)');
    c.fillStyle=hg;c.beginPath();c.arc(sh[0],sh[1],db,0,7);c.fill();c.globalCompositeOperation='source-over';
    bodyOrDot(c,sh[0],sh[1],'sat',MARK.drone*kl,S.sat,MARK.drone*2*kl*S.glow,kl);c.restore();   // drone ship size = MARK.drone (capped, ~rocket size)
  }

  // ================= SIZING / LOOP =================
  function drawMs(){return Math.max(2000,P.animDur*1000);}
  function drawFrame(head,phi,full,env,grow){ paint(ctx,W,H,head,phi,{transparent:false,full:full,env:env,grow:grow}); }
  function staticFull(){ drawFrame(lastHead(), camYaw, true); }

  var playing = !reduce, t0=null, rafId=null;
  function frame(now){ if(t0===null)t0=now; NOW=now; camPhi=camYaw+S.drift*Math.sin(now*CAM_W);
    var total=lastHead(), ph=((now-t0)/drawMs())%1; if(ph<0)ph+=1;
    var head=Math.max(1,Math.min(total,Math.round(ph*total)));
    drawFrame(head,camPhi,false);
    if(playing) rafId=raf(frame); }
  function play(){ if(playing && rafId!=null) return; playing=true; t0=null; rafId=raf(frame); }
  function pause(){ playing=false; caf(rafId); rafId=null; staticFull(); }

  function resize(w,h,ratio){
    w=Math.max(1,Math.round(w||0)); h=Math.max(1,Math.round(h||0));
    dpr = ratio || dprGet();
    W=w; H=h;
    canvas.style.width=w+'px'; canvas.style.height=h+'px';
    canvas.width=Math.round(w*dpr); canvas.height=Math.round(h*dpr);
    ctx.setTransform(dpr,0,0,dpr,0,0);
    if(!playing) staticFull();
  }

  // ================= INTERACTION (optional) =================
  var teardown=[];
  function on(el,ev,fn,opts){ el.addEventListener(ev,fn,opts); teardown.push(function(){el.removeEventListener(ev,fn,opts);}); }
  function fireCamera(){ if(onCamera) onCamera({tilt:S.tilt, yaw:camYaw, zoom:zoom, panX:panX, panY:panY}); }
  function attachInteractive(){
    var dragging=false,lastX=0,lastY=0;
    on(canvas,'pointerdown',function(ev){dragging=true;lastX=ev.clientX;lastY=ev.clientY;try{canvas.setPointerCapture(ev.pointerId);}catch(e){}});
    on(canvas,'pointermove',function(ev){if(!dragging)return;
      var dx=ev.clientX-lastX,dy=ev.clientY-lastY;lastX=ev.clientX;lastY=ev.clientY;
      if(ev.shiftKey||(ev.buttons&2)){panX+=dx;panY+=dy;}
      else{camYaw+=dx*0.006; S.tilt=Math.max(0,Math.min(88,S.tilt-dy*0.25));}
      fireCamera();
      if(!playing)drawFrame(lastHead(),camYaw,true);});
    on(canvas,'pointerup',function(){dragging=false;});
    on(canvas,'pointercancel',function(){dragging=false;});
    on(canvas,'contextmenu',function(ev){ev.preventDefault();});
    on(canvas,'wheel',function(ev){
      if(wheelModifierOnly && !ev.ctrlKey && !ev.metaKey)return;
      ev.preventDefault();
      var oz=zoom; zoom=Math.max(0.3,Math.min(40,zoom*Math.exp(-ev.deltaY*0.0012)));
      var w=canvas.clientWidth,h=canvas.clientHeight;
      panX+=(ev.offsetX-(w/2+panX))*(1-zoom/oz); panY+=(ev.offsetY-(h/2+panY))*(1-zoom/oz);
      fireCamera();
      if(!playing)drawFrame(lastHead(),camYaw,true);},{passive:false});
    on(canvas,'dblclick',function(){zoom=1;camYaw=0;panX=0;panY=0;fireCamera();if(!playing)drawFrame(lastHead(),camYaw,true);});
  }

  // ================= INIT =================
  compute();
  var iw = config.width || canvas.clientWidth || canvas.width || 800;
  var ih = config.height || canvas.clientHeight || canvas.height || 600;
  resize(iw, ih, config.dpr);
  if(interactive) attachInteractive();
  if(playing) play(); else staticFull();

  // ================= PUBLIC API =================
  return {
    // Live-update config. Pass {P:{...}} / {S:{...}} to merge, zoom/bscale to set,
    // recompute:true when a sim param (mode/preset/alt/inc/...) changed.
    setConfig: function(next){ next=next||{};
      if(next.P) assign(P, next.P);
      if(next.S) assign(S, next.S);
      if(next.zoom!=null) zoom=next.zoom;
      if(next.cx!=null) cxFrac=next.cx;
      if(next.cy!=null) cyFrac=next.cy;
      if(next.bscale!=null) bscaleVal=next.bscale;
      if(next.recompute) compute();
      if(!playing) staticFull(); },
    play: play,
    pause: pause,
    resize: resize,                                   // resize(cssW, cssH[, dpr])
    // Paint one frame into an arbitrary 2D context (used by the studio's PNG/video export).
    snapshot: function(targetCtx, w, h, opts){ paint(targetCtx, w, h, lastHead(), camYaw, assign({transparent:false, full:true}, opts||{})); },
    setBodyImage: function(which, img, url){ bodyImg[which]=img; bodyData[which]=url||null; if(!playing) staticFull(); },
    getState: function(){ return { P:P, S:S, zoom:zoom, camYaw:camYaw, panX:panX, panY:panY, satPeriod:satPeriod, traj:traj, NOW:NOW }; },
    isPlaying: function(){ return playing; },
    destroy: function(){ pause(); for(var i=0;i<teardown.length;i++) teardown[i](); teardown=[]; }
  };
}

export default { createViewer: createViewer };
if (typeof window !== 'undefined') window.P78Viewer = { createViewer: createViewer };
