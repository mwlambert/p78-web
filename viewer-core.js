/*! viewer-core.js — P78 cislunar mission viewer (simulation + renderer + loop).
 *
 *  Extracted from moon3.html so the viewer can run first-party in the page (no iframe).
 *  moon3.html stays the "studio" (controls + export) on top of this same core.
 *
 *  Usage (site / island):
 *    import { createViewer } from 'viewer-core';
 *    const v = createViewer(canvasEl, { interactive:false, P:{mode:'mission',...}, S:{...},
 *                                       labels:false, labelSet:['earth','moon','otv','tanker','depot'],
 *                                       onCamera:(cam)=>{}, onTelemetry:(t)=>{} });
 *    v.setConfig({ labels:true });   // live-toggle body labels
 *    v.resize(w, h);      // call from a ResizeObserver, or pass {width,height} in config
 *    v.pause(); v.play(); v.destroy();
 *
 *  onTelemetry(payload)  — called from the frame loop, throttled ~8 Hz, mission mode only. v1.1:
 *    { phase:'LEO'|'TLI'|'LLO', label, body:'earth'|'moon', progress:0..1,
 *      speed (km/s, vis-viva), altitude (km above primary surface),
 *      distToMoon / distToMoonSurface (km, centre / surface),
 *      distToEarth / distToEarthSurface (km, centre / surface),
 *      apoapsis, periapsis (km altitude), eccentricity, period (h),
 *      trueAnomaly (deg), flightPathAngle (deg),
 *      t (mission-elapsed days, real), tRemaining (days), version:'1.1', phaseChanged?:true }
 *    getState().telemetry returns the same payload for one-shot reads (no phaseChanged).
 *    All units/calcs are computed in-core (real two-body values); the host only renders.
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
  var camYaw=0, panX=0, panY=0, camPhi=0, renderPhi=0;   // renderPhi = the phi paint() is currently drawing at → lets bodyOrDot rotate a globe with the camera
  var cxFrac = config.cx!=null ? config.cx : 0.5;      // scene centre as a fraction of W/H (default 0.5 = middle).
  var cyFrac = config.cy!=null ? config.cy : 0.5;      // e.g. cy:0.7 drops the scene into the lower gap behind copy.
  var bscaleVal = config.bscale!=null ? config.bscale : 1;
  var markScale = config.markScale!=null ? config.markScale : 1;        // host multiplier for the depot/rocket/drone dot sizes (e.g. 0.4 on a zoomed-out backdrop). Strokes use lw.
  var labelScale = config.labelScale!=null ? config.labelScale : 1;     // host multiplier for body-label font size (default 1). Labels also track markScale gently (√) so they shrink with the dots on a backdrop.
  var labels = !!config.labels;                                         // draw a small label next to each body (default false)
  var labelSet = config.labelSet || null;                               // optional pick: ['earth','moon','depot','drone']; null = all
  var interactive = config.interactive !== false;                       // default true; site backdrop passes false
  var wheelModifierOnly = !!config.wheelModifierOnly;                    // for interactive embeds inside a scrolling page
  var onCamera = typeof config.onCamera==='function' ? config.onCamera : null;
  var onTelemetry = typeof config.onTelemetry==='function' ? config.onTelemetry : null;
  var TEL_VERSION='1.1', telHead=0, lastTel=0, TEL_MS=125, lastPhaseLabel=null;   // telemetry payload schema v1.1; emit ~8 Hz
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
    traj.moon=[];traj.sat=[];traj.prim=[];traj.tel=null;   // telemetry defined for mission mode only
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
    var sat=[],satTel=[],sumW=0,wk=[],j,tRun=0,nuS;                         // satTel: real orbital state per outbound sample (telemetry)
    var arcMeta=[{ph:'LEO',label:'LEO parking'},{ph:'LEO',label:'Raise to staging'},{ph:'LEO',label:'Staging orbit'}];
    for(kk=1;kk<=Nr;kk++)arcMeta.push({ph:'LEO',label:'Apogee raising'});
    arcMeta.push({ph:'TLI',label:'Trans-lunar injection'});
    for(kk=0;kk<arcs.length;kk++){wk[kk]=Math.sqrt(arcs[kk].dur);sumW+=wk[kk];}
    for(kk=0;kk<arcs.length;kk++){var ar=arcs[kk],st=Math.max(80,Math.round(2600*wk[kk]/sumW)),dt=ar.dur/st,mt=arcMeta[kk];
      for(j=0;j<st;j++){nuS=trueAnom(ar.M0+(ar.M1-ar.M0)*j/st,ar.e);sat.push(conic(ar.a,ar.e,nuS));
        satTel.push({ph:mt.ph,label:mt.label,body:'earth',r:ar.a*(1-ar.e*ar.e)/(1+ar.e*Math.cos(nuS)),a:ar.a,e:ar.e,nu:nuS,t:tRun});tRun+=dt;}}
    sat.push(conic(Et.a,Et.e,Math.PI));
    satTel.push({ph:'TLI',label:'Trans-lunar injection',body:'earth',r:Et.a*(1+Et.e),a:Et.a,e:Et.e,nu:Math.PI,t:tRun});
    var arrival=sat.length-1;
    var T_earth=0; for(kk=0;kk<arcs.length;kk++)T_earth+=arcs[kk].dur;
    var coast=Math.max(0.1,P.coast);
    var T_llo=periodDays(r_llo,muM), coils=Math.max(1,coast*Tmoon/(T_llo*P.periodMul));
    var earthSweep=TWO*T_earth/Tmoon, rate=earthSweep/arrival;
    var llo=Math.max(240,Math.min(16000,Math.round(coast*TWO/rate)));
    var startNu=Math.PI-earthSweep, moon=[],prim=[],all=[],tel=[],i,nu,mp,lc,frac,gi;
    for(i=0;i<=arrival;i++){nu=startNu+rate*i;mp=keplerPos(aMoon,eMoon,iMoon,0,0,nu);moon.push(mp);prim.push([0,0,0]);all.push(sat[i]);tel.push(satTel[i]);}
    var coilDur=coast*Tmoon, dtC=coilDur/Math.max(1,llo);                    // real time in LLO ≈ coast Moon-orbits
    for(i=1;i<=llo;i++){gi=arrival+i;nu=startNu+rate*gi;frac=i/llo;mp=keplerPos(aMoon,eMoon,iMoon,0,0,nu);moon.push(mp);prim.push(mp);tRun+=dtC;
      lc=keplerPos(r_llo,0,incL,0,0,TWO*coils*frac);all.push([mp[0]+lloMag*lc[0],mp[1]+lloMag*lc[1],mp[2]+lloMag*lc[2]]);
      tel.push({ph:'LLO',label:'Low lunar orbit',body:'moon',r:r_llo,a:r_llo,e:0,nu:(TWO*coils*frac)%TWO,t:tRun});}
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
      var sumR=0,wr=[],gidx=arrival+llo,j2,pR,nuR;
      var rMeta=[{ph:'TLI',label:'Trans-Earth injection'}];
      for(kk=Nr;kk>=1;kk--)rMeta.push({ph:'LEO',label:'Apogee lowering'});
      rMeta.push({ph:'LEO',label:'Staging orbit'});rMeta.push({ph:'LEO',label:'Descend to LEO'});rMeta.push({ph:'LEO',label:'LEO parking'});
      for(kk=0;kk<rarcs.length;kk++){wr[kk]=Math.sqrt(rarcs[kk].dur);sumR+=wr[kk];}
      for(kk=0;kk<rarcs.length;kk++){var rc=rarcs[kk],stR=Math.max(80,Math.round(2600*wr[kk]/sumR)),dtR=rc.dur/stR,rmt=rMeta[kk];
        for(j2=0;j2<stR;j2++){nuR=trueAnom(rc.M0+(rc.M1-rc.M0)*j2/stR,rc.e);pR=rot(conic(rc.a,rc.e,nuR));
          gidx++;nu=startNu+rate*gidx;mp=keplerPos(aMoon,eMoon,iMoon,0,0,nu);moon.push(mp);prim.push([0,0,0]);all.push(pR);tRun+=dtR;
          tel.push({ph:rmt.ph,label:rmt.label,body:'earth',r:rc.a*(1-rc.e*rc.e)/(1+rc.e*Math.cos(nuR)),a:rc.a,e:rc.e,nu:nuR,t:tRun});}}
      var lastIdx=moon.length-1, curSweep=rate*lastIdx;
      traj.missionOrbits=curSweep/TWO;
      var padN=Math.round((Math.ceil(curSweep/TWO-1e-6)*TWO-curSweep)/rate);
      var dtP=rate/TWO*Tmoon, padLaps=Math.max(1,Math.round(padN/100)), dLeoAng=TWO*padLaps/padN;   // OTV keeps ORBITING LEO through the wait (schematic lap rate; real speed lives in telemetry). Whole laps → seam matches the start.
      for(i=1;i<=padN;i++){gi=lastIdx+i;nu=startNu+rate*gi;mp=keplerPos(aMoon,eMoon,iMoon,0,0,nu);tRun+=dtP;
        moon.push(mp);prim.push([0,0,0]);all.push(rot(conic(r_leo,0,dLeoAng*i)));
        tel.push({ph:'LEO',label:'LEO parking',body:'earth',r:r_leo,a:r_leo,e:0,nu:dLeoAng*i,t:tRun});}
    }
    traj.moon=moon;traj.prim=prim;traj.sat=all;traj.tel=tel;
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
  var imgTexCache={};   // equirectangular body photo → ImageData for shadedGlobe sphere-mapping; cached per image src
  function imgTex(which,im){var e=imgTexCache[which];if(!e||e.src!==im.src){var cv=document.createElement('canvas');cv.width=im.naturalWidth;cv.height=im.naturalHeight;cv.getContext('2d').drawImage(im,0,0);e={src:im.src,day:texData(cv),lights:null};imgTexCache[which]=e;}return e;}
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
        var nz=Math.sqrt(1-r2);                                          // sphere normal toward the viewer
        var v=0.5+Math.asin(nyd)/Math.PI;                                // true latitude → poles converge to points (no polar smear)
        var u=(0.5+Math.atan2(nx,nz)/6.2831853+frac)%1;if(u<0)u+=1;      // true longitude → foreshortens toward the limb
        var tx=(u*tw)|0,ty=(v*th)|0;if(ty<0)ty=0;if(ty>=th)ty=th-1;if(tx>=tw)tx=tw-1;var to=(ty*tw+tx)*4;
        var br,tf;
        if(flat){br=1-0.32*r2;}
        else{var lam=nx*sr+(-nyd)*su+nz*sv;tf=lam+0.14;tf=tf<0?0:tf>0.28?1:tf/0.28;br=ambient+(1-ambient)*tf;}
        data[o]=td[to]*br;data[o+1]=td[to+1]*br;data[o+2]=td[to+2]*br;data[o+3]=255;
        if(ld&&!flat){var la=ld[to+3];if(la>0){var ad=(la/255)*(0.45+0.55*(1-tf));
          data[o]=cl255(data[o]+ld[to]*ad);data[o+1]=cl255(data[o+1]+ld[to+1]*ad);data[o+2]=cl255(data[o+2]+ld[to+2]*ad);}}
      }}
    bx.putImageData(img,0,0);
    c.save();c.beginPath();c.arc(x,y,R,0,7);c.clip();c.drawImage(buf.cv,x-R,y-R);c.restore();}
  function drawGlobe(c,x,y,R,day,lights,rot,isEarth,hex,blur,sCam,flat){
    shadedGlobe(c,x,y,R,day,lights,rot,sCam,isEarth?0.05:0.015,flat);}
  // A full-disc photo is ALREADY an orthographic view of the sphere, so pixel↔normal is 1:1 — no texture
  // mapping needed. Sample the photo directly and light it by the true normal, giving a real terminator/phase.
  // (This is how the Moon gets sunlight without an equirectangular map.)
  function shadedDisc(c,x,y,R,dayD,sCam,ambient,flat){
    var d=Math.max(4,Math.ceil(2*R)),buf=SGBUF(d),bx=buf.ctx,img=bx.createImageData(d,d),data=img.data;
    var tw=dayD.width,th=dayD.height,td=dayD.data,sr=sCam[0],su=sCam[1],sv=sCam[2],px,py,o;
    for(py=0;py<d;py++){var nyd=(py+0.5-R)/R,ty=((py/d)*th)|0;if(ty>=th)ty=th-1;
      for(px=0;px<d;px++){var nx=(px+0.5-R)/R,r2=nx*nx+nyd*nyd;o=(py*d+px)*4;
        if(r2>1){data[o+3]=0;continue;}
        var tx=((px/d)*tw)|0;if(tx>=tw)tx=tw-1;var to=(ty*tw+tx)*4;
        var br;
        if(flat){br=1-0.32*r2;}
        else{var nz=Math.sqrt(1-r2),lam=nx*sr+(-nyd)*su+nz*sv,tf=lam+0.14;tf=tf<0?0:tf>0.28?1:tf/0.28;br=ambient+(1-ambient)*tf;}
        data[o]=td[to]*br;data[o+1]=td[to+1]*br;data[o+2]=td[to+2]*br;data[o+3]=255;
      }}
    bx.putImageData(img,0,0);
    c.save();c.beginPath();c.arc(x,y,R,0,7);c.clip();c.drawImage(buf.cv,x-R,y-R);c.restore();}
  // Earth: blue Rayleigh halo (real atmosphere, leans to the sunlit limb). Moon: airless, so its glow is a faint
  // neutral bloom (camera glare), deliberately tighter+weaker than Earth's. Scales with S.glow; S.glow=0 disables.
  var hbuf={};
  function HBUF(d){var b=hbuf[d];if(!b){var cv=document.createElement('canvas');cv.width=d;cv.height=d;b={cv:cv,ctx:cv.getContext('2d')};hbuf[d]=b;}return b;}
  function bodyHalo(c,x,y,R,sCam,flat,isEarth){var gm=(S.glow==null?1:S.glow);if(gm<=0||R<=0)return;
    var s=sCam||[-0.6,0.5,0.6];
    var out=isEarth?1.26:1.14,col=isEarth?'95,165,255':'214,226,240';
    // Composited offscreen: the night-side fade below needs destination-out, which on the main canvas
    // would erase the starfield showing through the ring. Build it in a buffer, then add it with 'lighter'.
    var D=Math.max(8,Math.ceil(2*R*out)),b=HBUF(D),bc=b.ctx,cx=D/2,cy=D/2,bR=D/(2*out);
    bc.setTransform(1,0,0,1,0,0);bc.clearRect(0,0,D,D);bc.globalCompositeOperation='source-over';
    var ox=flat?cx:cx+s[0]*bR*0.10,oy=flat?cy:cy-s[1]*bR*0.10;
    var g=bc.createRadialGradient(ox,oy,bR*0.97,cx,cy,bR*out);
    g.addColorStop(0,'rgba('+col+','+(isEarth?0.55:0.20)*gm+')');
    g.addColorStop(0.38,'rgba('+col+','+(isEarth?0.22:0.07)*gm+')');
    g.addColorStop(1,'rgba('+col+',0)');
    // Ring only (disc punched out): additive blue over bright cloud just washes to white, so keep the
    // halo outside the limb where it reads against space — which is where atmosphere is actually visible.
    bc.save();bc.beginPath();bc.arc(cx,cy,bR*out,0,6.2831853);bc.moveTo(cx+bR*0.995,cy);bc.arc(cx,cy,bR*0.995,0,6.2831853,true);bc.clip();   // moveTo is required: without it canvas joins the two arcs with a straight line and notches the ring
    bc.fillStyle=g;bc.fillRect(0,0,D,D);bc.restore();
    if(!flat){   // Sun on: air only scatters where it's lit, so fade the halo out across the terminator (screen-space sun dir = [sr,-su])
      var lx=s[0],ly=-s[1],m=Math.hypot(lx,ly);
      if(m>1e-4){lx/=m;ly/=m;
        var lg=bc.createLinearGradient(cx+lx*bR*out,cy+ly*bR*out,cx-lx*bR*out,cy-ly*bR*out);
        lg.addColorStop(0,'rgba(0,0,0,0)');lg.addColorStop(0.5,'rgba(0,0,0,0.55)');lg.addColorStop(1,'rgba(0,0,0,1)');
        bc.globalCompositeOperation='destination-out';bc.fillStyle=lg;bc.fillRect(0,0,D,D);bc.globalCompositeOperation='source-over';}}
    c.save();c.globalCompositeOperation='lighter';c.drawImage(b.cv,x-cx,y-cy);c.restore();}
  var SUNW=(function(){var v=[0.68,-0.42,0.60],m=Math.hypot(v[0],v[1],v[2]);return[v[0]/m,v[1]/m,v[2]/m];})();
  function sunCam(phi){var tl=S.tilt*DEG,ct=Math.cos(tl),st=Math.sin(tl),cph=Math.cos(phi),sph=Math.sin(phi);
    var rx=SUNW[0]*cph-SUNW[1]*sph,y1=SUNW[0]*sph+SUNW[1]*cph;
    return [rx, y1*ct-SUNW[2]*st, y1*st+SUNW[2]*ct];}
  function bodyOrDot(c,x,y,which,dotR,hex,blur,k,lit,sCam){var im=bodyImg[which];
    if(im&&im.complete&&im.naturalWidth){
      if(which==='earth'||which==='moon'){var IT=imgTex(which,im),BR=dotR*bscale(),isE=(which==='earth'),amb=isE?0.05:0.015;
        // Pick the treatment from the image itself rather than the body: a 2:1 equirectangular map gets
        // sphere-mapped into a rotating globe; a ~square full-disc photo is already an orthographic view,
        // so it's lit by the true normal instead. Either asset works for either body.
        if(im.naturalWidth>=im.naturalHeight*1.7)
          shadedGlobe(c,x,y,BR,IT.day,IT.lights,-renderPhi/6.2831853+NOW*(isE?0.0000038:0.0000016),sCam||[-0.6,0.5,0.6],amb,!P.sun);
        else
          shadedDisc(c,x,y,BR,IT.day,sCam||[-0.6,0.5,0.6],amb,!P.sun);
        bodyHalo(c,x,y,BR,sCam,!P.sun,isE);return;}
      var d=2*dotR*bscale();c.save();c.beginPath();c.arc(x,y,d/2,0,7);c.clip();c.drawImage(im,x-d/2,y-d/2,d,d);var lg=c.createRadialGradient(x,y,d*0.36,x,y,d/2);lg.addColorStop(0,'rgba(0,0,0,0)');lg.addColorStop(0.7,'rgba(0,0,0,0)');lg.addColorStop(1,'rgba(0,0,0,0.55)');c.fillStyle=lg;c.fillRect(x-d/2,y-d/2,d,d);c.restore();return;}   // non-globe image (e.g. sat icon): flat clipped disc + limb
    if(which==='earth'||which==='moon'){var T=which==='earth'?earthTex():moonTex();
      drawGlobe(c,x,y,dotR,T.day,T.lights,NOW*(which==='earth'?0.0000038:0.0000016),which==='earth',hex,blur,sCam||[-0.6,0.5,0.6],!P.sun);
      bodyHalo(c,x,y,dotR,sCam,!P.sun,which==='earth');return;}
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
  function drawLaunch(c,pr,bp,ring,inc,dPhase,dRate,seed,k,lf){
    var PER=20000, MIS=9000;                                               // 9 s mission, then ~11 s idle (≈ one depot orbit) before the next tanker
    var tm=((NOW+seed*PER)%PER+PER)%PER; if(tm>MIS)return; var cyc=tm/MIS;  // cyc 0..1 across the active mission; seed staggers the two tankers
    var dAng=dPhase+dRate*NOW, rS=ring*0.11;
    var ud=keplerPos(1,0,inc,0,0,dAng), th=keplerPos(1,0,inc,0,0,dAng+Math.PI/2);
    var O=[bp[0]+ring*ud[0],bp[1]+ring*ud[1],bp[2]+ring*ud[2]];             // depot (RDV point)
    function cbz(A,B,C,D,u){var m=1-u,a=m*m*m,b=3*m*m*u,d=3*m*u*u,e=u*u*u;
      return [a*A[0]+b*B[0]+d*C[0]+e*D[0],a*A[1]+b*B[1]+d*C[1]+e*D[1],a*A[2]+b*B[2]+d*C[2]+e*D[2]];}
    var pos;
    if(cyc<0.33){                                                          // ASCENT: pad → depot (gravity-turn)
      var ul=keplerPos(1,0,inc,0,0,dAng-0.9);
      var L =[bp[0]+rS*ul[0],bp[1]+rS*ul[1],bp[2]+rS*ul[2]];
      var A1=[bp[0]+ring*0.5*ul[0],bp[1]+ring*0.5*ul[1],bp[2]+ring*0.5*ul[2]];
      var A2=[O[0]-ring*0.5*th[0],O[1]-ring*0.5*th[1],O[2]-ring*0.5*th[2]];
      pos=cbz(L,A1,A2,O,cyc/0.33);
    } else if(cyc<0.63){ pos=O; }                                          // RDV: docked at the depot
    else {                                                                 // DESCENT: depot → surface (return, lands downrange)
      var dl=keplerPos(1,0,inc,0,0,dAng+0.9);
      var Ld=[bp[0]+rS*dl[0],bp[1]+rS*dl[1],bp[2]+rS*dl[2]];
      var D1=[O[0]+ring*0.5*th[0],O[1]+ring*0.5*th[1],O[2]+ring*0.5*th[2]];
      var D2=[bp[0]+ring*0.5*dl[0],bp[1]+ring*0.5*dl[1],bp[2]+ring*0.5*dl[2]];
      pos=cbz(O,D1,D2,Ld,(cyc-0.63)/0.37);
    }
    var p=pr(pos);dot(c,p[0],p[1],MARK.rocket*k,'#ffffff',MARK.rocket*1.4*k*S.glow);   // rocket = plain white; size = MARK.rocket
    if(lf&&labeled('tanker'))drawLabel(c,p[0],p[1],'Tanker',-(MARK.rocket*k+10),lf);}        // tanker label to the LEFT of the rocket
  function fillBg(c,W,H){c.fillStyle=S.bg;c.fillRect(0,0,W,H);}
  function bgDepth(c,W,H){var g=c.createRadialGradient(W/2,H*0.46,0,W/2,H*0.46,Math.max(W,H)*0.62);
    g.addColorStop(0,'rgba(30,42,70,0.22)');g.addColorStop(0.5,'rgba(14,20,36,0.12)');g.addColorStop(1,'rgba(0,0,0,0)');
    c.fillStyle=g;c.fillRect(0,0,W,H);}
  // The depth gradient spans only ~15 brightness levels across hundreds of px, so on 8-bit panels it
  // quantises into visible concentric rings (obvious on cheap/TN screens, invisible on a good one).
  // Dither it: add sub-level noise so pixels round to either side of a step and the band edges dissolve.
  var noiseCv=null;
  function noiseTile(){if(!noiseCv){var n=64,cv=document.createElement('canvas');cv.width=n;cv.height=n;
      var g2=cv.getContext('2d'),im=g2.createImageData(n,n),d=im.data,i,v,seed=987654321;
      for(i=0;i<n*n;i++){seed=(seed*1103515245+12345)&0x7fffffff;v=(seed/0x7fffffff*255)|0;
        d[i*4]=v;d[i*4+1]=v;d[i*4+2]=v;d[i*4+3]=255;}
      g2.putImageData(im,0,0);noiseCv=cv;}return noiseCv;}
  function bgDither(c,W,H){   // pattern is built per call (cheap) so this is safe on export/snapshot contexts too
    c.save();c.globalCompositeOperation='lighter';c.globalAlpha=0.014;   // ~±2 levels: kills the rings, mean lift is imperceptible
    c.fillStyle=c.createPattern(noiseTile(),'repeat');c.fillRect(0,0,W,H);c.restore();}
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
  function labeled(key){ return labels && (!labelSet || labelSet.indexOf(key)>=0); }
  function drawLabel(c,x,y,text,off,lf){                                 // small mono label offset off the body; off<0 → placed to the left
    c.save();c.font=lf+'px ui-monospace, SFMono-Regular, Menlo, monospace';c.textAlign=off<0?'right':'left';c.textBaseline='middle';
    c.shadowColor='rgba(0,0,0,0.7)';c.shadowBlur=3;                     // subtle backing so text stays legible over lines/stars
    c.fillStyle='rgba(220,228,242,0.92)';c.fillText(text, x+off, y);c.restore(); }
  function paint(c,W,H,head,phi,o){
    o=o||{};renderPhi=phi;var k=skf(W,H)*zoom,kl=skf(W,H),mk=kl*markScale,lf=Math.max(9,Math.min(15,Math.round(11*kl*Math.sqrt(markScale)*labelScale))),total=lastHead();if(!o.transparent){fillBg(c,W,H);bgDepth(c,W,H);bgDither(c,W,H);drawStars(c,W,H,phi);}   // k = bodies (·zoom); kl = strokes (constant); mk = dot markers (constant · markScale); lf = label font px
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
    if(labeled('earth'))drawLabel(c,eP[0],eP[1],'Earth',eR+10,lf);
    var spts=[];for(i=0;i<=total;i++)spts.push(pr(satPlot(i)));
    if(P.showTrail)trailPaint(c,spts,head,total,hexRGB(S.sat),kl,o.full,occ,o.env,o.grow);   // kl → constant trail thickness
    bodyOrDot(c,mP[0],mP[1],'moon',mR,S.moon,8*k*S.glow,k,'#eef2f8',sCam);
    if(labeled('moon'))drawLabel(c,mP[0],mP[1],'Moon',mR+10,lf);
    if(P.showSats){var j,A,bp,rad,inc,ang,uu,asp;for(j=0;j<AMBS.length;j++){A=AMBS[j];
      if(A.body===0){bp=[0,0,0];rad=STAGE_R;inc=P.inc*DEG;}
      else{bp=traj.moon[head];rad=P.mag*(R_M+(P.mode==='mission'?P.lloAlt:P.alt));inc=(P.mode==='mission'?P.lloInc:P.inc)*DEG;}
      ang=A.phase+A.rate*NOW;uu=keplerPos(rad,0,inc,0,0,ang);
      asp=pr([bp[0]+uu[0],bp[1]+uu[1],bp[2]+uu[2]]);if(occ(asp))continue;twinkleDot(c,asp[0],asp[1],MARK.depot*mk,'#e6bf5c','#e6bf5c',MARK.depot*0.7*mk*S.glow);
      if(labeled('depot'))drawLabel(c,asp[0],asp[1],'Depot',MARK.depot*mk+10,lf);}}   // depot = flat gold (no bright core); size = MARK.depot · markScale
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
        if(occ(fp))continue;bodyOrDot(c,fp[0],fp[1],'sat',MARK.drone*mk,S.sat,MARK.drone*2*mk*S.glow,mk);}}   // escorts = same size as the main drone (MARK.drone · markScale)
    if(P.showHop){
      drawLaunch(c,pr,traj.moon[head], P.mag*(R_M+(P.mode==='mission'?P.lloAlt:P.alt)), (P.mode==='mission'?P.lloInc:P.inc)*DEG, AMBS[1].phase, AMBS[1].rate, 0.20, mk, lf);
      drawLaunch(c,pr,[0,0,0], STAGE_R, P.inc*DEG, AMBS[0].phase, AMBS[0].rate, 0.66, mk, lf);}   // mk → rockets sized by MARK.rocket · markScale
    if(P.showLag){var mw=traj.moon[head],md=Math.hypot(mw[0],mw[1],mw[2])||1,ux=mw[0]/md,uy=mw[1]/md,uz=mw[2]/md;
      drawLag(c,pr([mw[0]-lagR*ux,mw[1]-lagR*uy,mw[2]-lagR*uz]),'L1',k);
      drawLag(c,pr([mw[0]+lagR*ux,mw[1]+lagR*uy,mw[2]+lagR*uz]),'L2',k);}
    var sh=spts[head];c.save();c.globalAlpha=(o.env==null?1:o.env);
    var db=MARK.drone*2.3*mk;   // drone-head bloom radius (MARK.drone · markScale)
    c.globalCompositeOperation='lighter';var hg=c.createRadialGradient(sh[0],sh[1],0,sh[0],sh[1],db);
    hg.addColorStop(0,'rgba('+hexRGB(S.sat)+',0.55)');hg.addColorStop(0.5,'rgba('+hexRGB(S.sat)+',0.14)');hg.addColorStop(1,'rgba('+hexRGB(S.sat)+',0)');
    c.fillStyle=hg;c.beginPath();c.arc(sh[0],sh[1],db,0,7);c.fill();c.globalCompositeOperation='source-over';
    bodyOrDot(c,sh[0],sh[1],'sat',MARK.drone*mk,S.sat,MARK.drone*2*mk*S.glow,mk);c.restore();   // drone ship size = MARK.drone · markScale
    if(labeled('otv'))drawLabel(c,sh[0],sh[1],'OTV',MARK.drone*mk+10,lf);   // OTV = the orbital transfer vehicle
  }

  // ================= SIZING / LOOP =================
  function drawMs(){return Math.max(2000,P.animDur*1000);}
  function drawFrame(head,phi,full,env,grow){ telHead=head; paint(ctx,W,H,head,phi,{transparent:false,full:full,env:env,grow:grow}); }
  function staticFull(){ drawFrame(lastHead(), camYaw, true); }

  var playing = !reduce, t0=null, rafId=null;
  function frame(now){ if(t0===null)t0=now; NOW=now; camPhi=camYaw+S.drift*Math.sin(now*CAM_W);
    var total=lastHead(), ph=((now-t0)/drawMs())%1; if(ph<0)ph+=1;
    var head=Math.max(1,Math.min(total,Math.round(ph*total)));
    drawFrame(head,camPhi,false);
    if(now-lastTel>=TEL_MS){ lastTel=now; fireTelemetry(head); }   // throttled telemetry (~8 Hz)
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
  // ---- telemetry: real mission state (vis-viva units) for a host HUD; mission mode only. All calcs live here. ----
  function telemetry(head){
    var t=traj.tel; if(P.mode!=='mission'||!t||!t.length) return null;
    var n=t.length-1, h=Math.max(0,Math.min(n,Math.round(head||0))), r=t[h];
    var mu=r.body==='moon'?muM:muE, R=r.body==='moon'?R_M:R_E;
    var v=Math.sqrt(Math.max(0,mu*(2/r.r-1/r.a)));                    // vis-viva speed, km/s
    // real spacecraft position: earth-phase samples are true; in LLO divide the coil offset back out of the magnified render
    var mw=traj.moon[h], sw=traj.sat[h], sx,sy,sz;
    if(r.body==='moon'){ var mg=P.mag||1; sx=mw[0]+(sw[0]-mw[0])/mg; sy=mw[1]+(sw[1]-mw[1])/mg; sz=mw[2]+(sw[2]-mw[2])/mg; }
    else { sx=sw[0]; sy=sw[1]; sz=sw[2]; }
    var dMoon=Math.hypot(sx-mw[0],sy-mw[1],sz-mw[2]);                 // centre-to-centre, km
    var dEarth=Math.hypot(sx,sy,sz);
    var fpa=Math.atan2(r.e*Math.sin(r.nu),1+r.e*Math.cos(r.nu))/DEG;  // flight-path angle (deg): 0 = local horizontal (circular / apsis)
    var ta=(((r.nu%TWO)+TWO)%TWO)/DEG;
    return {phase:r.ph, label:r.label, body:r.body, progress:n>0?h/n:0,
      speed:Math.round(v*1000)/1000,                                 // km/s
      altitude:Math.round(r.r-R),                                    // km above the current primary's surface
      distToMoon:Math.round(dMoon), distToMoonSurface:Math.round(dMoon-R_M),      // km (centre / surface)
      distToEarth:Math.round(dEarth), distToEarthSurface:Math.round(dEarth-R_E),  // km (centre / surface)
      apoapsis:Math.round(r.a*(1+r.e)-R), periapsis:Math.round(r.a*(1-r.e)-R),    // km altitude of the current orbit
      eccentricity:Math.round(r.e*1e4)/1e4,
      period:Math.round(periodDays(r.a,mu)*24*1000)/1000,            // orbital period of the current arc, hours
      trueAnomaly:Math.round(ta*10)/10,                              // deg
      flightPathAngle:Math.round(fpa*10)/10,                         // deg
      t:Math.round(r.t*100)/100,                                     // mission-elapsed days (real)
      tRemaining:Math.round((t[n].t-r.t)*100)/100,                   // days to loop/mission end (real)
      version:TEL_VERSION};
  }
  function fireTelemetry(head){ if(!onTelemetry) return; var p=telemetry(head); if(!p) return;
    if(p.label!==lastPhaseLabel){ p.phaseChanged=true; lastPhaseLabel=p.label; }   // first tick after a leg transition
    onTelemetry(p); }
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
      if(next.markScale!=null) markScale=next.markScale;
      if(next.labelScale!=null) labelScale=next.labelScale;
      if(next.labels!=null) labels=!!next.labels;
      if(next.labelSet!==undefined) labelSet=next.labelSet||null;
      if(next.recompute) compute();
      if(!playing) staticFull(); },
    play: play,
    pause: pause,
    resize: resize,                                   // resize(cssW, cssH[, dpr])
    // Paint one frame into an arbitrary 2D context (used by the studio's PNG/video export).
    snapshot: function(targetCtx, w, h, opts){ paint(targetCtx, w, h, lastHead(), camYaw, assign({transparent:false, full:true}, opts||{})); },
    setBodyImage: function(which, img, url){ bodyImg[which]=img; bodyData[which]=url||null; if(!playing) staticFull(); },
    getState: function(){ return { P:P, S:S, zoom:zoom, camYaw:camYaw, panX:panX, panY:panY, satPeriod:satPeriod, traj:traj, NOW:NOW, telemetry:telemetry(telHead) }; },
    isPlaying: function(){ return playing; },
    destroy: function(){ pause(); for(var i=0;i<teardown.length;i++) teardown[i](); teardown=[]; }
  };
}

export default { createViewer: createViewer };
if (typeof window !== 'undefined') window.P78Viewer = { createViewer: createViewer };
