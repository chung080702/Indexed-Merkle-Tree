import { buildPoseidon } from "circomlibjs";

export class IndexedMerkleTree {
    constructor(n) {
        this.height = n;
        this.node = {};
        this.leaves = [];
        this.hasher = {}
    }

    hash(array) {
        var hash = this.hasher;
        return hash.F.toString(hash(array));
    }

    async init() {
        this.hasher = await buildPoseidon();

        var zero = [0, 33];
        zero[0] = this.hash([0, 0, 0]);

        for (var i = 1; i <= this.height; i++) {
            zero[i] = this.hash([zero[i - 1], zero[i - 1]]);

        }
        this.zero = zero;
        this.node[1] = zero[this.height];
        this.leaves.push({ val: 0, nextVal: 0, nextIdx: 0 });
    }



    getRoot() {
        return this.node[1];
    }

    trueIndex(i) {
        return i + (1 << this.height);
    }

    leftIndex(i) {
        return (i << 1);
    }

    rightIndex(i) {
        return (i << 1) + 1;
    }

    parentIndex(i) {
        return (i >> 1);
    }

    sibling(i) {
        var index = i ^ 1;

        var value = this.getValueNode(index);
        return value;
    }

    getValueNode(index) {
        if (this.node[index] != undefined) return this.node[index];
        else {

            for (var i = this.height; i >= 0; i--)
                if ((index >> i) & 1) {

                    return this.zero[this.height - i];
                }

        }

    }

    update(idx) {

        var leaf = this.leaves[idx];
        var index = this.trueIndex(idx);
        var node = this.node;
        node[index] = this.hash([leaf.val, leaf.nextVal, leaf.nextIdx]);
        while (index > 1) {
            index = this.parentIndex(index);
            var indexLeft = this.leftIndex(index);
            var indexRight = this.rightIndex(index);
            node[index] = this.hash([this.getValueNode(indexLeft), this.getValueNode(indexRight)]);
        }
    }

    getLeafLow(value) {
        if (value < 0) return;
        var leafLow = this.leaves[0];
        var idxLow = 0;
        while (true) {
            if (leafLow.nextVal > value || leafLow.nextVal == 0) break;
            idxLow = leafLow.nextIdx;
            leafLow = this.leaves[leafLow.nextIdx];
        }
        return { idxLow, leafLow }
    }

    insert(value) {

        var { idxLow, leafLow } = this.getLeafLow(value);
        if (leafLow == value) return;
        ///
        var { path: pathLow, root: rootOld } = this.getPath(leafLow.val)

        ///
        var leafNew = { val: value, nextVal: leafLow.nextVal, nextIdx: leafLow.nextIdx };
        leafLow.nextVal = value;
        leafLow.nextIdx = this.leaves.length;
        var idxNew = this.leaves.length;
        this.leaves.push(leafNew);
        this.update(idxLow);

        this.update(idxNew);
        var { path: pathNew, root: rootNew } = this.getPath(value);

        return {
            pathLow,
            rootOld,
            indexLow: idxLow,
            valLow: leafLow.val,
            nextValLow: leafNew.nextVal,
            nextIdxLow: leafNew.nextIdx,

            valNew: value,
            idxNew: idxNew,

            pathNew,
            rootNew
        }
    }

    insert_batch(m, values) {
        values.sort();
        var idxNew = this.leaves.length;
        var p = values.length;

        if (idxNew % p != 0 || (1 << m) != p) {
            return;
        }

        var pathLow = [];
        var idxLow = [];
        var valLow = [];
        var nextValLow = [];
        var nextIdxLow = [];

        var valNew = [];
        var nextValNew = [];
        var nextIdxNew = [];
        var rootOld = this.getRoot();
        // insert to pending subtree

        for (var i = 0; i < p; i++) {
            var value = values[i];
            var { idxLow: curIndexLow, leafLow } = this.getLeafLow(value);
            if (leafLow.val == value) return;
            ///
            var { path } = this.getPath(leafLow.val);
            idxLow.push(curIndexLow);
            pathLow.push(path);
            valLow.push(leafLow.val);
            nextValLow.push(leafLow.nextVal);
            nextIdxLow.push(leafLow.nextIdx);
            ///
            var leafNew = { val: value, nextVal: leafLow.nextVal, nextIdx: leafLow.nextIdx };
            leafLow.nextVal = value;
            leafLow.nextIdx = this.leaves.length;
            this.leaves.push(leafNew);
            if (curIndexLow < idxNew) this.update(curIndexLow);

            valNew.push(leafNew.val);

        }

        for (var i = 0; i < p; i++) {
            var leaf = this.leaves[i + idxNew];

            nextValNew.push(leaf.nextVal);
            nextIdxNew.push(leaf.nextIdx);
        }

        // insert subtree

        //      get path

        var index = this.trueIndex(idxNew) >> m;


        var pathNew = [];
        while (index > 1) {
            pathNew.push(this.sibling(index));
            index = this.parentIndex(index);
        }



        //    insert subtree
        for (var i = 0; i < p; i++) {
            this.update(idxNew + i);
        }

        index = this.trueIndex(idxNew) >> m;



        var rootNew = this.getRoot();
        return {
            pathLow,
            rootOld,
            indexLow: idxLow,
            valLow,
            nextValLow,
            nextIdxLow,

            rootOld,
            rootNew,

            indexNew: idxNew,
            pathNew,
            valNew,
            nextValNew,
            nextIdxNew
        }
    }


    getPath(value) {

        var { idxLow, leafLow } = this.getLeafLow(value);

        if (leafLow == value) return;
        var index = this.trueIndex(idxLow);
        var path = [];

        while (index > 1) {
            path.push(this.sibling(index));
            index = this.parentIndex(index);
        }

        return { leaf: leafLow, path, index: idxLow, root: this.getRoot() };
    }

    stringify(s) {
        return this.hash.F.toString(s);
    }


}
