pragma circom 2.0.0;

include "../../node_modules/circomlib/circuits/poseidon.circom";
include "../../node_modules/circomlib/circuits/bitify.circom";
include "../../node_modules/circomlib/circuits/comparators.circom";


function getZero(i) {
    if (i==0) return 5317387130258456662214331362918410991734007599705406860481038345552731150762;
    else if (i==1) return 5301900180746108365834837840355741695167403565517259206503735319173783315742;
    else if (i==2) return 19759440382600727929415049642887307143518671081639244670052489500787514850212;
    else if (i==3) return 11575399251628151734428362828441614938772848828475906566857213866326592241179;
    else if (i==4) return 6632555919090241659299800894218068745568431736196896666697681740099319754273;
    else if (i==5) return 2313232035512824863888346564211238648697583940443483502600731472911335817854;
    else if (i==6) return 12219166190744012474665556054784140979314676975916090596913570678231824844496;
    else if (i==7) return 16146864604902996392229526390577377437180881860230124064882884440248322100339;
    else if (i==8) return 6883543445806624803603297055410892317599264946303553983246148642156945721809;
    else if (i==9) return 11376031557295681140127084012245938798408060888509383225192187436273860950878;
    else if (i==10) return 13241605803954237324747758640385138335781780544452364878098724458062976117242;
    else if (i==11) return 17855149516804167337625231993818327714748909580849949294952537831754058414670;
    else if (i==12) return 5150255556564484319136269061916843962561348275990403501481125286754601797805;
    else if (i==13) return 6987786980040962217323608240860512602136308242543772977912408457104385595406;
    else if (i==14) return 12673791472672914327028296381717349631548592060758239087545042240348016593302;
    else if (i==15) return 9311366817918121883031003818542895863321158352954515731060536796838219379679;
    else if (i==16) return 19585342603050165772395358149453302999296038452416557172220992666065524588903;
    else if (i==17) return 8275043704423853810900845936958744738316525212865659311257431212306169446045;
    else if (i==18) return 16186914510693313963181937763227692521094695382771382196248944425969899233840;
    else if (i==19) return 767287730589592697964997275831534428290387386582193516309984231823744273525;
    else if (i==20) return 8182961934280185552908516081891354585128675946832334410314642727305953230495;
    else if (i==21) return 14553789876728003050984909720833228345703341783942046413329913248389004034924;
    else if (i==22) return 6278449848160193613534961101404674224795668202070703678497109778769228770164;
    else if (i==23) return 8979671514355837952844943277614674271246740514273131428387277329861932324931;
    else if (i==24) return 21571534543733545789815777004636730528838914284333679118902566390287667028570;
    else if (i==25) return 18924195170311205995329199132962258629761263537596441216670202833476308740987;
    else if (i==26) return 19135056793797297106895003927293911553715031470085451353297367444045593886226;
    else if (i==27) return 19880802233039501694132273141007514078082675668582073994501231061064322422311;
    else if (i==28) return 13981684304997822704186619219231220214101708822880409798804837787926320255246;
    else if (i==29) return 9114362048964899084797815362621027676695169625694813982057199762506308222437;
    else if (i==30) return 16119926292128498499760018714973489263785338035469823266838928430729854428132;
    else if (i==31) return 9066247990074734647376987472974149870232401410809652492321935259087598384293;
    else return 775389356373991272891944630989602693981420205035441183290348903863870890005;
}


template AllCorrect(n) {
    signal input in[n];
    signal mul[n];
     
    mul[0] <== in[0];
    for (var i = 1; i < n; i++) {
        mul[i] <== mul[i-1] * in[i];
    }

    signal output out <== mul[n-1];
}

template CalRoot(n) {
    signal input path[n];
    signal input index;
    signal input leaf;
   

    signal indexBits[n] <== Num2Bits(n)(index);
    signal node[n+1];
    signal left[n];
    signal right[n+1];
    
    node[0] <== leaf;
    
    for (var i = 0; i < n; i++) {
        left[i] <== node[i] + indexBits[i] * (path[i] - node[i]);
        right[i] <== path[i] + indexBits[i] * (node[i] - path[i]);
        node[i+1] <== Poseidon(2)([left[i], right[i]]);

    }
    
    signal output out <== node[n];
}
template VerifyMTP(n) {
    signal input path[n];
    signal input root;
    signal input index;
    signal input leaf;
   
    signal expected_root <== CalRoot(n)(path,index,leaf);
    
    signal output out <== IsEqual()([expected_root, root]);
    
}

template CheckLow() {
    signal input in[3];
    signal x <==  LessThan(252)([in[0],in[1]]);
    signal y <==  LessThan(252)([in[1],in[2]]);
    signal z <== IsZero()(in[2]);

    signal output out <== x * (y+z);
}

template CheckNonMembership(n) {
    signal input path[n];
    signal input root;
    signal input index;
    signal input val;
    signal input nextVal;
    signal input nextIdx;

    signal input curVal;

    signal leaf <== Poseidon(3)([val,nextVal,nextIdx]);

    signal a <== CheckLow()([val,curVal,nextVal]);
    signal b <== VerifyMTP(n)(path,root,index,leaf);
    signal output out <== a * b;
}

template CheckMembership(n) {
    signal input path[n];
    signal input root;
    signal input index;
    signal input val;
    signal input nextVal;
    signal input nextIdx;
    
    signal leaf <== Poseidon(3)([val,nextVal,nextIdx]);
    signal output out <== VerifyMTP(n)(path,root,index,leaf);

}

template Insert(n) {
    signal input rootOld;

    // low nullifier
    signal input pathLow[n];
    signal input indexLow;
    signal input valLow;
    signal input nextValLow;
    signal input nextIdxLow;

    // new nullifier
    signal input valNew;
    signal input idxNew;
    signal input pathNew[n];
    signal input rootNew;
    
    // check non membership new nullifier 
    signal a <== CheckNonMembership(n)(pathLow,rootOld,indexLow,valLow,nextValLow, nextIdxLow,valNew);
    // update low nullifier
    signal leafLowNew <== Poseidon(3)([valLow,valNew,idxNew]);
    signal rootCur <== CalRoot(n)(pathLow, indexLow, leafLowNew);

    // update new nullifier
    signal b <== VerifyMTP(n)(pathNew,rootCur,idxNew,getZero(0));


    signal c <== CheckMembership(n)(pathNew,rootNew,idxNew,valNew,nextValLow,nextIdxLow);
    
    a === 1;
    b === 1;
    c === 1;
}


template InsertBatch(n,m) {
    // m: height of subtree
    var p = 1 << m; 
    
    signal input pathLow[p][n];
    signal input indexLow[p];
    signal input valLow[p];
    signal input nextValLow[p];
    signal input nextIdxLow[p];

    signal input rootOld;
    signal input rootNew;

    signal input indexNew; // begin index
    signal input pathNew[n-m]; // path subtree
    signal input valNew[p];
    signal input nextValNew[p];
    signal input nextIdxNew[p];

    // check sorted range new nullifiers
    
    signal a[p];
    for (var i = 1; i < p; i++) {
        a[i] <== LessThan(252)([valNew[i-1],valNew[i]]);
        a[i] === 1;
    }
    
    signal root[p+1];

    root[0] <== rootOld;
    signal lowInSubTree[p];
    signal lowNotInSubTree[p];
    signal b[p][3];
    signal c[p][6];
    signal d[p];
    // insert new nullifer to subtree
    for (var i = 0; i < p; i++) {
        
        if (i > 0) {   
            // low not in subtree -> check non membership
            b[i][0] <== CheckNonMembership(n)(pathLow[i],root[i],indexLow[i],valLow[i],nextValLow[i], nextIdxLow[i], valNew[i]);
            b[i][1] <== IsEqual()([nextValNew[i-1], nextValLow[i-1]]);
            b[i][2] <== IsEqual()([nextIdxNew[i-1], nextIdxLow[i-1]]);
            
            lowNotInSubTree[i] <== AllCorrect(3)(b[i]);

            // low in subtree -> low is pre valNew
            c[i][0] <== IsEqual()([valNew[i-1], valLow[i]]);
            c[i][1] <== IsEqual()([nextValNew[i-1], valNew[i]]);
            c[i][2] <== IsEqual()([nextIdxNew[i-1], indexNew + i]); 
            c[i][3] <== IsEqual()([nextValLow[i-1], nextValLow[i]]);
            c[i][4] <== IsEqual()([nextIdxLow[i-1], nextIdxLow[i]]);
            c[i][5] <== CheckLow()([valLow[i], valNew[i], nextValLow[i]]);
            
            lowInSubTree[i] <== AllCorrect(6)(c[i]);            
        }
        else  {
            lowNotInSubTree[i] <== CheckNonMembership(n)(pathLow[i],root[i],indexLow[i],valLow[i],nextValLow[i], nextIdxLow[i], valNew[i]);
            lowInSubTree[i] <== 0;
        }
        
        lowInSubTree[i] + lowNotInSubTree[i] === 1;

        // update root
        d[i] <== CalRoot(n)(pathLow[i],indexLow[i], Poseidon(3)([valLow[i], valNew[i], indexNew + i]));
        root[i+1] <== root[i] + lowNotInSubTree[i] * (d[i] - root[i]);   
        
    }

    
    // check empty subtree
   
    signal indexSubTree <-- indexNew >> m;
    indexNew === indexSubTree * p;
    signal e <== VerifyMTP(n-m)(pathNew, root[p], indexSubTree, getZero(m));
    e === 1;

    // cal root subtree
    signal node[p*2];
    for (var i = 0; i < p; i++) {
        node[i+p] <== Poseidon(3)([valNew[i],nextValNew[i],nextIdxNew[i]]);
    }

    for (var i = p-1 ; i > 0; i--) {
        node[i] <== Poseidon(2)([node[i*2], node[i*2 +1]]); 
        // -> node[1] is root subtree
    }

    
    // Check update subtree

    signal f <== VerifyMTP(n-m)(pathNew, rootNew, indexSubTree, node[1]);
    f === 1;

}



