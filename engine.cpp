// ============================================================================
//  BitEngine v3.4 FINAL — WASM/Termux, Phone-optimized (4GB RAM)
//  Changes vs v3.3:
//    [1] TT_BITS 20 → 19 (8MB instead of 16MB — better L2 cache on phones)
//    [2] __builtin_prefetch for TT lookup
//    [3] UCI now parses "position ... moves ..." correctly
//    [4] checkExtStack[0] initialized explicitly
//  Build:
//    emcc engine.cpp -O3 -std=c++17 -flto \
//      -s WASM=1 -s MODULARIZE=1 -s EXPORT_NAME="createEngine" \
//      -s ALLOW_MEMORY_GROWTH=1 -s INITIAL_MEMORY=64MB -s FILESYSTEM=0 \
//      -s EXPORTED_FUNCTIONS='["_engine_init","_engine_set_fen","_engine_get_fen", \
//        "_engine_search","_engine_get_score","_engine_get_depth","_engine_get_nodes", \
//        "_engine_get_time","_engine_get_side","_engine_in_check","_engine_get_halfmove", \
//        "_engine_gen_legal","_engine_get_legal","_engine_make","_engine_unmake", \
//        "_engine_move_from","_engine_move_to","_engine_move_promo", \
//        "_engine_game_status","_engine_perft","_engine_set_silent","_malloc","_free"]' \
//      -s EXPORTED_RUNTIME_METHODS='["ccall","cwrap","UTF8ToString","stringToUTF8"]' \
//      -o engine.js
// ============================================================================
#include <cstdint>
#include <cstring>
#include <cstdio>
#include <iostream>
#include <cstdlib>
#include <string>
#include <algorithm>
#include <chrono>
#include <vector>

using U64 = uint64_t;

// ---- Enums ----
enum Color { WHITE, BLACK, COLOR_NB };
enum PieceType { PAWN, KNIGHT, BISHOP, ROOK, QUEEN, KING, PT_NB };
enum Piece { W_PAWN,W_KNIGHT,W_BISHOP,W_ROOK,W_QUEEN,W_KING,
             B_PAWN,B_KNIGHT,B_BISHOP,B_ROOK,B_QUEEN,B_KING,
             PIECE_NB, NO_PIECE = PIECE_NB };
inline Piece mkPiece(Color c, PieceType pt) { return Piece(c*6+pt); }
inline Color pcColor(Piece p) { return p >= 6 ? BLACK : WHITE; }
inline PieceType pcType(Piece p) { return PieceType(p % 6); }

enum Square {
    A1,B1,C1,D1,E1,F1,G1,H1, A2,B2,C2,D2,E2,F2,G2,H2,
    A3,B3,C3,D3,E3,F3,G3,H3, A4,B4,C4,D4,E4,F4,G4,H4,
    A5,B5,C5,D5,E5,F5,G5,H5, A6,B6,C6,D6,E6,F6,G6,H6,
    A7,B7,C7,D7,E7,F7,G7,H7, A8,B8,C8,D8,E8,F8,G8,H8,
    NO_SQ = 64
};
inline int fileOf(int s) { return s & 7; }
inline int rankOf(int s) { return s >> 3; }
inline int mkSq(int f, int r) { return r*8+f; }

// ---- Bit helpers ----
inline int popcnt(U64 b) { return __builtin_popcountll(b); }
inline int lsb(U64 b)    { return __builtin_ctzll(b); }
inline int msb(U64 b)    { return 63 - __builtin_clzll(b); }
inline int poplsb(U64& b){ int s = lsb(b); b &= b-1; return s; }
constexpr U64 bit(int s) { return 1ULL << s; }

constexpr U64 FILE_A = 0x0101010101010101ULL;
constexpr U64 RANK_1 = 0xFFULL;
constexpr U64 RANK_3 = RANK_1 << 16;
constexpr U64 RANK_6 = RANK_1 << 40;
constexpr U64 RANK_7 = RANK_1 << 48;
constexpr U64 RANK_8 = RANK_1 << 56;

// ---- Attack tables ----
U64 PawnAtt[COLOR_NB][64];
U64 KnightAtt[64];
U64 KingAtt[64];

// Classical rays
U64 RayN[64], RayE[64], RayS[64], RayW[64];
U64 RayNE[64], RayNW[64], RaySE[64], RaySW[64];

static void initRays() {
    for (int sq = 0; sq < 64; sq++) {
        int f = sq & 7, r = sq >> 3;
        U64 a;
        a=0; for (int i=1; r+i<=7; i++) a |= 1ULL << ((r+i)*8+f); RayN[sq]=a;
        a=0; for (int i=1; r-i>=0; i--) a |= 1ULL << ((r-i)*8+f); RayS[sq]=a;
        a=0; for (int i=1; f+i<=7; i++) a |= 1ULL << (r*8+f+i);   RayE[sq]=a;
        a=0; for (int i=1; f-i>=0; i--) a |= 1ULL << (r*8+f-i);   RayW[sq]=a;
        a=0; for (int i=1; r+i<=7 && f+i<=7; i++) a |= 1ULL << ((r+i)*8+f+i); RayNE[sq]=a;
        a=0; for (int i=1; r+i<=7 && f-i>=0; i--) a |= 1ULL << ((r+i)*8+f-i); RayNW[sq]=a;
        a=0; for (int i=1; r-i>=0 && f+i<=7; i++) a |= 1ULL << ((r-i)*8+f+i); RaySE[sq]=a;
        a=0; for (int i=1; r-i>=0 && f-i>=0; i--) a |= 1ULL << ((r-i)*8+f-i); RaySW[sq]=a;
    }
}

inline U64 rookAtt(int sq, U64 occ) {
    U64 r, b, att = 0;
    r = RayN[sq]; b = occ & r; if (b) r ^= RayN[lsb(b)]; att |= r;
    r = RayS[sq]; b = occ & r; if (b) r ^= RayS[msb(b)]; att |= r;
    r = RayE[sq]; b = occ & r; if (b) r ^= RayE[lsb(b)]; att |= r;
    r = RayW[sq]; b = occ & r; if (b) r ^= RayW[msb(b)]; att |= r;
    return att;
}
inline U64 bishopAtt(int sq, U64 occ) {
    U64 r, b, att = 0;
    r = RayNE[sq]; b = occ & r; if (b) r ^= RayNE[lsb(b)]; att |= r;
    r = RayNW[sq]; b = occ & r; if (b) r ^= RayNW[lsb(b)]; att |= r;
    r = RaySE[sq]; b = occ & r; if (b) r ^= RaySE[msb(b)]; att |= r;
    r = RaySW[sq]; b = occ & r; if (b) r ^= RaySW[msb(b)]; att |= r;
    return att;
}
inline U64 queenAtt(int sq, U64 occ) { return rookAtt(sq, occ) | bishopAtt(sq, occ); }

static void initLeapers() {
    static const int KND[8][2]={{1,2},{2,1},{2,-1},{1,-2},{-1,-2},{-2,-1},{-2,1},{-1,2}};
    static const int KGD[8][2]={{1,0},{1,1},{0,1},{-1,1},{-1,0},{-1,-1},{0,-1},{1,-1}};
    for (int s = 0; s < 64; s++) {
        int f0 = fileOf(s), r0 = rankOf(s);
        U64 nA=0, kA=0;
        for (int i = 0; i < 8; i++) {
            int f = f0+KND[i][1], r = r0+KND[i][0];
            if (f>=0&&f<8&&r>=0&&r<8) nA |= bit(mkSq(f,r));
            f = f0+KGD[i][1]; r = r0+KGD[i][0];
            if (f>=0&&f<8&&r>=0&&r<8) kA |= bit(mkSq(f,r));
        }
        KnightAtt[s] = nA; KingAtt[s] = kA;
        U64 wp=0, bp=0;
        if (f0>0){ if(r0<7) wp|=bit(mkSq(f0-1,r0+1)); if(r0>0) bp|=bit(mkSq(f0-1,r0-1)); }
        if (f0<7){ if(r0<7) wp|=bit(mkSq(f0+1,r0+1)); if(r0>0) bp|=bit(mkSq(f0+1,r0-1)); }
        PawnAtt[WHITE][s]=wp; PawnAtt[BLACK][s]=bp;
    }
}

// ---- Zobrist ----
U64 Zp[PIECE_NB][64], Zc[16], Zep[8], Zside;
static void initZobrist() {
    U64 s = 0x9E3779B97F4A7C15ULL;
    auto next=[&](){ s^=s>>12; s^=s<<25; s^=s>>27; return s*0x2545F4914F6CDD1DULL; };
    for (int p=0;p<PIECE_NB;p++) for (int sq=0;sq<64;sq++) Zp[p][sq]=next();
    for (int i=0;i<16;i++) Zc[i]=next();
    for (int i=0;i<8;i++) Zep[i]=next();
    Zside=next();
}

// ---- Move ----
using Move = uint16_t;
constexpr Move MOVE_NONE = 0;
inline Move mkMove(int from, int to, int promo=0, int flag=0) {
    return Move(from | (to<<6) | (promo<<12) | (flag<<14));
}
inline int mFrom(Move m) { return m & 63; }
inline int mTo(Move m)   { return (m>>6) & 63; }
inline int mPromo(Move m){ return (m>>12) & 7; }
inline int mFlag(Move m) { return (m>>14) & 3; }

// ---- Position ----
struct Position {
    U64 pieces[2][6];
    U64 occ[2];
    U64 all;
    Color side;
    int castling;
    Square ep;
    int halfmove, fullmove;
    U64 hash;
    Square kingSq[2];
    Move lastMove;
    U64 histHash[1024];
    int histCount;

    void setFen(const std::string& fen);
    std::string toFen() const;
    void computeHash();
    bool isAttacked(Square s, Color by) const;
    bool inCheck(Color c) const { return isAttacked(kingSq[c], Color(c^1)); }
};

inline Piece pieceOn(const Position& pos, Square s) {
    for (int c=0;c<2;c++) for (int pt=0;pt<6;pt++)
        if (pos.pieces[c][pt] & bit(s)) return mkPiece(Color(c), PieceType(pt));
    return NO_PIECE;
}
static void putPiece(Position& pos, Piece p, Square s) {
    pos.pieces[pcColor(p)][pcType(p)] |= bit(s);
    pos.occ[pcColor(p)] |= bit(s);
    pos.all |= bit(s);
}
static void removePiece(Position& pos, Piece p, Square s) {
    pos.pieces[pcColor(p)][pcType(p)] &= ~bit(s);
    pos.occ[pcColor(p)] &= ~bit(s);
    pos.all &= ~bit(s);
}

void Position::computeHash() {
    U64 h=0;
    for (int c=0;c<2;c++) for (int pt=0;pt<6;pt++) {
        U64 b = pieces[c][pt];
        while (b) { int s = poplsb(b); h ^= Zp[mkPiece(Color(c),PieceType(pt))][s]; }
    }
    h ^= Zc[castling];
    if (ep != NO_SQ) h ^= Zep[fileOf(ep)];
    if (side == BLACK) h ^= Zside;
    hash = h;
}

bool Position::isAttacked(Square s, Color by) const {
    if (PawnAtt[by^1][s] & pieces[by][PAWN]) return true;
    if (KnightAtt[s] & pieces[by][KNIGHT]) return true;
    if (KingAtt[s] & pieces[by][KING]) return true;
    if (bishopAtt(s, all) & (pieces[by][BISHOP] | pieces[by][QUEEN])) return true;
    if (rookAtt(s, all) & (pieces[by][ROOK] | pieces[by][QUEEN])) return true;
    return false;
}

void Position::setFen(const std::string& fen) {
    memset(this, 0, sizeof(Position));
    for (int c=0;c<2;c++) kingSq[c] = NO_SQ;
    side = WHITE; castling = 0; ep = NO_SQ; halfmove = 0; fullmove = 1;
    lastMove = MOVE_NONE;

    int idx = 56;
    size_t i = 0;
    for (; i < fen.size() && fen[i] != ' '; i++) {
        char c = fen[i];
        if (c == '/') { idx -= 16; continue; }
        if (c >= '1' && c <= '8') { idx += c - '0'; continue; }
        Color col = (c >= 'A' && c <= 'Z') ? WHITE : BLACK;
        char up = (c >= 'a') ? char(c - 32) : c;
        PieceType pt;
        switch (up) {
            case 'P': pt=PAWN; break;   case 'N': pt=KNIGHT; break;
            case 'B': pt=BISHOP; break; case 'R': pt=ROOK; break;
            case 'Q': pt=QUEEN; break;  case 'K': pt=KING; break;
            default: continue;
        }
        Piece p = mkPiece(col, pt);
        putPiece(*this, p, Square(idx));
        if (pt == KING) kingSq[col] = Square(idx);
        idx++;
    }
    if (i < fen.size()) i++;
    if (i < fen.size()) { side = (fen[i]=='b') ? BLACK : WHITE; while (i < fen.size() && fen[i]!=' ') i++; }
    if (i < fen.size()) i++;
    if (i < fen.size()) {
        for (; i < fen.size() && fen[i] != ' '; i++) {
            switch (fen[i]) {
                case 'K': castling|=1; break; case 'Q': castling|=2; break;
                case 'k': castling|=4; break; case 'q': castling|=8; break;
            }
        }
    }
    if (i < fen.size()) i++;
    if (i < fen.size() && fen[i] != '-') {
        int f = fen[i]-'a', r = fen[i+1]-'1';
        ep = Square(mkSq(f, r));
        i += 2;
    }
    while (i < fen.size() && fen[i]==' ') i++;
    if (i < fen.size()) { halfmove = atoi(fen.c_str()+i); while (i<fen.size() && fen[i]!=' ') i++; }
    while (i < fen.size() && fen[i]==' ') i++;
    if (i < fen.size()) fullmove = atoi(fen.c_str()+i);

    computeHash();
    histCount = 0;
    histHash[histCount++] = hash;
}

std::string Position::toFen() const {
    static const char* P2C = "PNBRQKpnbrqk";
    std::string s;
    for (int r = 7; r >= 0; r--) {
        int empty = 0;
        for (int f = 0; f < 8; f++) {
            Piece p = pieceOn(*this, Square(mkSq(f, r)));
            if (p == NO_PIECE) empty++;
            else { if (empty) { s += char('0'+empty); empty = 0; } s += P2C[p]; }
        }
        if (empty) s += char('0'+empty);
        if (r) s += '/';
    }
    s += ' '; s += (side==WHITE?'w':'b'); s += ' ';
    std::string c;
    if (castling&1) c+='K'; if (castling&2) c+='Q';
    if (castling&4) c+='k'; if (castling&8) c+='q';
    s += c.empty() ? "-" : c;
    s += ' ';
    if (ep == NO_SQ) s += '-';
    else { s += char('a'+fileOf(ep)); s += char('1'+rankOf(ep)); }
    s += ' ' + std::to_string(halfmove) + ' ' + std::to_string(fullmove);
    return s;
}

// ---- Move generation ----
struct MoveList {
    Move moves[256];
    int count = 0;
    void add(Move m) { moves[count++] = m; }
};

static void genPawnMoves(const Position& pos, MoveList& ml, Color us, bool capsOnly) {
    U64 pawns = pos.pieces[us][PAWN];
    U64 empty = ~pos.all;
    U64 enemies = pos.occ[us^1];
    int push = (us == WHITE) ? 8 : -8;
    U64 rank8 = (us == WHITE) ? RANK_8 : RANK_1;
    int startRank = (us == WHITE) ? 1 : 6;

    U64 b = pawns;
    while (b) {
        int from = poplsb(b);
        if (!capsOnly) {
            int to = from + push;
            if (bit(to) & empty) {
                if (bit(to) & rank8) {
                    ml.add(mkMove(from,to,QUEEN)); ml.add(mkMove(from,to,ROOK));
                    ml.add(mkMove(from,to,BISHOP)); ml.add(mkMove(from,to,KNIGHT));
                } else {
                    ml.add(mkMove(from,to));
                    if (rankOf(from) == startRank) {
                        int to2 = to + push;
                        if (bit(to2) & empty) ml.add(mkMove(from, to2, 0, 1));
                    }
                }
            }
        }
        U64 att = PawnAtt[us][from] & enemies;
        while (att) {
            int t = poplsb(att);
            if (bit(t) & rank8) {
                ml.add(mkMove(from,t,QUEEN)); ml.add(mkMove(from,t,ROOK));
                ml.add(mkMove(from,t,BISHOP)); ml.add(mkMove(from,t,KNIGHT));
            } else ml.add(mkMove(from,t));
        }
        if (pos.ep != NO_SQ && (PawnAtt[us][from] & bit(pos.ep)))
            ml.add(mkMove(from, pos.ep, 0, 2));
    }
}

static void genPieceMoves(const Position& pos, MoveList& ml, Color us, PieceType pt, bool capsOnly) {
    U64 b = pos.pieces[us][pt];
    U64 target = capsOnly ? pos.occ[us^1] : ~pos.occ[us];
    while (b) {
        int from = poplsb(b);
        U64 att = 0;
        switch (pt) {
            case KNIGHT: att = KnightAtt[from]; break;
            case BISHOP: att = bishopAtt(from, pos.all); break;
            case ROOK:   att = rookAtt(from, pos.all);   break;
            case QUEEN:  att = queenAtt(from, pos.all);  break;
            case KING:   att = KingAtt[from];            break;
            default: break;
        }
        att &= target;
        while (att) ml.add(mkMove(from, poplsb(att)));
    }
}

static void genCastling(const Position& pos, MoveList& ml) {
    Color us = pos.side;
    if (us == WHITE) {
        if ((pos.castling&1) && !(pos.all & (bit(F1)|bit(G1)))
            && !pos.isAttacked(E1,BLACK) && !pos.isAttacked(F1,BLACK) && !pos.isAttacked(G1,BLACK))
            ml.add(mkMove(E1,G1,0,3));
        if ((pos.castling&2) && !(pos.all & (bit(B1)|bit(C1)|bit(D1)))
            && !pos.isAttacked(E1,BLACK) && !pos.isAttacked(D1,BLACK) && !pos.isAttacked(C1,BLACK))
            ml.add(mkMove(E1,C1,0,3));
    } else {
        if ((pos.castling&4) && !(pos.all & (bit(F8)|bit(G8)))
            && !pos.isAttacked(E8,WHITE) && !pos.isAttacked(F8,WHITE) && !pos.isAttacked(G8,WHITE))
            ml.add(mkMove(E8,G8,0,3));
        if ((pos.castling&8) && !(pos.all & (bit(B8)|bit(C8)|bit(D8)))
            && !pos.isAttacked(E8,WHITE) && !pos.isAttacked(D8,WHITE) && !pos.isAttacked(C8,WHITE))
            ml.add(mkMove(E8,C8,0,3));
    }
}

static void genMoves(const Position& pos, MoveList& ml, bool capsOnly = false) {
    genPawnMoves(pos, ml, pos.side, capsOnly);
    genPieceMoves(pos, ml, pos.side, KNIGHT, capsOnly);
    genPieceMoves(pos, ml, pos.side, BISHOP, capsOnly);
    genPieceMoves(pos, ml, pos.side, ROOK, capsOnly);
    genPieceMoves(pos, ml, pos.side, QUEEN, capsOnly);
    genPieceMoves(pos, ml, pos.side, KING, capsOnly);
    if (!capsOnly) genCastling(pos, ml);
}

// ---- Make / Unmake ----
struct UndoInfo {
    int castling;
    Square ep;              // ← تغيّر من int
    int halfmove, fullmove;
    U64 hash;
    Piece captured;
    Move lastMove;
    int histIdx;
};

static void makeMove(Position& pos, Move m, UndoInfo& u) {
    int from = mFrom(m), to = mTo(m), promo = mPromo(m), flag = mFlag(m);
    u.castling = pos.castling; u.ep = pos.ep;
    u.halfmove = pos.halfmove; u.fullmove = pos.fullmove;
    u.hash = pos.hash; u.captured = NO_PIECE;
    u.lastMove = pos.lastMove; u.histIdx = pos.histCount;

    Color us = pos.side, them = Color(us^1);
    Piece moving = pieceOn(pos, Square(from));

    if (pos.ep != NO_SQ) pos.hash ^= Zep[fileOf(pos.ep)];

    Square capSq = Square(to);
    if (flag == 2) capSq = Square(us==WHITE ? to-8 : to+8);
    if (flag != 3 && (pos.all & bit(capSq))) {
        Piece cap = pieceOn(pos, capSq);
        if (cap != NO_PIECE) {
            u.captured = cap;
            removePiece(pos, cap, capSq);
            pos.hash ^= Zp[cap][capSq];
        }
    }

    removePiece(pos, moving, Square(from));
    pos.hash ^= Zp[moving][from];

    if (promo) {
        Piece newP = mkPiece(us, PieceType(promo));
        putPiece(pos, newP, Square(to));
        pos.hash ^= Zp[newP][to];
    } else {
        putPiece(pos, moving, Square(to));
        pos.hash ^= Zp[moving][to];
    }

    if (flag == 3) {
        int rf, rt;
        if (to==G1){rf=H1;rt=F1;} else if (to==C1){rf=A1;rt=D1;}
        else if (to==G8){rf=H8;rt=F8;} else {rf=A8;rt=D8;}
        Piece rk = pieceOn(pos, Square(rf));
        removePiece(pos, rk, Square(rf));
        putPiece(pos, rk, Square(rt));
        pos.hash ^= Zp[rk][rf] ^ Zp[rk][rt];
    }

    if (pcType(moving) == KING) pos.kingSq[us] = Square(to);

    int newCast = pos.castling;
    if (from==E1||to==E1) newCast &= ~3;
    if (from==E8||to==E8) newCast &= ~12;
    if (from==A1||to==A1) newCast &= ~2;
    if (from==H1||to==H1) newCast &= ~1;
    if (from==A8||to==A8) newCast &= ~8;
    if (from==H8||to==H8) newCast &= ~4;
    if (newCast != pos.castling) {
        pos.hash ^= Zc[pos.castling] ^ Zc[newCast];
        pos.castling = newCast;
    }

    pos.ep = NO_SQ;
    if (flag == 1) {
        pos.ep = Square(us==WHITE ? to-8 : to+8);
        pos.hash ^= Zep[fileOf(pos.ep)];
    }

    if (pcType(moving) == PAWN || u.captured != NO_PIECE) pos.halfmove = 0;
    else pos.halfmove++;

    pos.side = them;
    pos.hash ^= Zside;
    if (us == BLACK) pos.fullmove++;
    pos.lastMove = m;

    if (pos.histCount < 1024) pos.histHash[pos.histCount++] = pos.hash;
}

static void unmakeMove(Position& pos, Move m, const UndoInfo& u) {
    int from = mFrom(m), to = mTo(m), promo = mPromo(m), flag = mFlag(m);
    Color us = Color(pos.side ^ 1);

    pos.side = us;
    pos.castling = u.castling; pos.ep = u.ep;
    pos.halfmove = u.halfmove; pos.fullmove = u.fullmove;
    pos.hash = u.hash; pos.lastMove = u.lastMove; pos.histCount = u.histIdx;

    Piece onTo = pieceOn(pos, Square(to));
    if (onTo != NO_PIECE) removePiece(pos, onTo, Square(to));
    Piece moved = promo ? mkPiece(us, PAWN) : onTo;
    putPiece(pos, moved, Square(from));

    if (pcType(moved) == KING) pos.kingSq[us] = Square(from);

    if (u.captured != NO_PIECE) {
        Square capSq = Square(to);
        if (flag == 2) capSq = Square(us==WHITE ? to-8 : to+8);
        putPiece(pos, u.captured, capSq);
    }

    if (flag == 3) {
        int rf, rt;
        if (to==G1){rf=H1;rt=F1;} else if (to==C1){rf=A1;rt=D1;}
        else if (to==G8){rf=H8;rt=F8;} else {rf=A8;rt=D8;}
        Piece rk = pieceOn(pos, Square(rt));
        if (rk != NO_PIECE) {
            removePiece(pos, rk, Square(rt));
            putPiece(pos, rk, Square(rf));
        }
    }
}

// ---- SEE ----
static const int PieceValue[PT_NB] = {100, 320, 330, 500, 900, 20000};

bool seeGE(const Position& pos, Move m, int threshold) {
    int from = mFrom(m), to = mTo(m), promo = mPromo(m), flag = mFlag(m);
    Square capSq = Square(to);
    if (flag == 2) capSq = Square(pos.side==WHITE ? to-8 : to+8);

    int gain[32];
    gain[0] = 0;
    if (flag != 3 && (pos.all & bit(capSq))) {
        Piece cap = pieceOn(pos, capSq);
        if (cap != NO_PIECE) gain[0] = PieceValue[pcType(cap)];
    }
    if (promo) gain[0] += PieceValue[promo] - PieceValue[PAWN];
    if (gain[0] < threshold) return false;

    Piece attacker = pieceOn(pos, Square(from));
    int attackerValue = attacker != NO_PIECE ? PieceValue[pcType(attacker)] : 0;

    U64 occ = pos.all;
    occ &= ~bit(from);
    occ &= ~bit(capSq);

    Color stm = Color(pos.side ^ 1);
    int d = 0;
    while (d < 31) {
        int lvaSq = -1, lvaVal = 0, lvaType = -1;
        U64 pawns = PawnAtt[stm^1][to] & pos.pieces[stm][PAWN] & occ;
        if (pawns) { lvaSq = lsb(pawns); lvaVal = PieceValue[PAWN]; lvaType = PAWN; }
        if (lvaType < 0) { U64 kn = KnightAtt[to] & pos.pieces[stm][KNIGHT] & occ;
            if (kn) { lvaSq = lsb(kn); lvaVal = PieceValue[KNIGHT]; lvaType = KNIGHT; } }
        if (lvaType < 0) { U64 bs = bishopAtt(to, occ) & pos.pieces[stm][BISHOP] & occ;
            if (bs) { lvaSq = lsb(bs); lvaVal = PieceValue[BISHOP]; lvaType = BISHOP; } }
        if (lvaType < 0) { U64 rk = rookAtt(to, occ) & pos.pieces[stm][ROOK] & occ;
            if (rk) { lvaSq = lsb(rk); lvaVal = PieceValue[ROOK]; lvaType = ROOK; } }
        if (lvaType < 0) { U64 qn = queenAtt(to, occ) & pos.pieces[stm][QUEEN] & occ;
            if (qn) { lvaSq = lsb(qn); lvaVal = PieceValue[QUEEN]; lvaType = QUEEN; } }
        if (lvaType < 0) { U64 kg = KingAtt[to] & pos.pieces[stm][KING] & occ;
            if (kg) { lvaSq = lsb(kg); lvaVal = PieceValue[KING]; lvaType = KING; } }
        if (lvaType < 0) break;

        d++;
        gain[d] = attackerValue - gain[d-1];
        attackerValue = lvaVal;
        occ ^= bit(lvaSq);
        stm = Color(stm ^ 1);
    }
    while (d > 0) { gain[d-1] = -std::max(-gain[d-1], gain[d]); d--; }
    return gain[0] >= threshold;
}

// ---- Evaluation ----
static const int MatMG[PT_NB] = {82, 337, 365, 477, 1025, 0};
static const int MatEG[PT_NB] = {94, 281, 297, 512, 936, 0};
static const int PhaseW[PT_NB] = {0, 1, 1, 2, 4, 0};

static const int PST_MG[6][64] = {
    { 0,0,0,0,0,0,0,0, 98,134,61,95,68,126,34,-11, -6,7,26,31,65,56,25,-20,
     -14,13,6,21,23,12,17,-23, -27,-2,-5,12,17,6,10,-25, -26,-4,-4,-10,3,3,33,-12,
     -35,-1,-20,-23,-15,24,38,-22, 0,0,0,0,0,0,0,0 },
    { -167,-89,-34,-49,61,-97,-15,-107, -73,-41,72,36,23,62,7,-17, -47,60,37,65,84,129,73,44,
      -9,17,19,53,37,69,18,22, -13,4,16,13,28,19,21,-8, -23,-9,12,10,19,17,25,-16,
      -29,-53,-12,-3,-1,18,-14,-19, -105,-21,-58,-33,-17,-28,-19,-23 },
    { -29,4,-82,-37,-25,-42,7,-8, -26,16,-18,-13,30,59,18,-47, -16,37,43,40,35,50,37,-2,
      -4,5,19,50,37,37,7,-2, -6,13,13,26,34,12,10,4, 0,15,15,15,14,27,18,10,
      4,15,16,0,7,21,33,1, -33,-3,-14,-21,-13,-12,-39,-21 },
    { 32,42,32,51,63,9,31,43, 27,32,58,62,80,67,26,44, -5,19,26,36,17,45,61,16,
      -24,-11,7,26,24,35,-8,-20, -36,-26,-12,-1,9,-7,6,-23, -45,-25,-16,-17,3,0,-5,-33,
      -44,-16,-20,-9,-1,11,-6,-71, -19,-13,1,17,16,7,-37,-26 },
    { -28,0,29,12,59,44,43,45, -24,-39,-5,1,-16,57,28,54, -13,-17,7,8,29,56,47,57,
      -27,-27,-16,-16,-1,17,-2,1, -9,-26,-9,-10,-2,-4,3,-3, -14,2,-11,-2,-5,2,14,5,
      -35,-8,11,2,8,15,-3,1, -1,-18,-9,10,-15,-25,-31,-50 },
    { -65,23,16,-15,-56,-34,2,13, 29,-1,-20,-7,-8,-4,-38,-29, -9,24,2,-16,-20,6,22,-22,
      -17,-20,-12,-27,-30,-25,-14,-36, -49,-1,-27,-39,-46,-44,-33,-51, -14,-14,-22,-46,-44,-30,-15,-27,
      1,7,-8,-64,-43,-16,9,8, -15,36,12,-54,8,-28,24,14 }
};
static const int PST_EG[6][64] = {
    { 0,0,0,0,0,0,0,0, 178,173,158,134,147,132,165,187, 94,100,85,67,56,53,82,84,
      32,24,13,5,-2,4,17,17, 13,9,-3,-7,-7,-8,3,-1, 4,7,-6,1,0,-5,-1,-8,
      13,8,8,10,13,0,2,-7, 0,0,0,0,0,0,0,0 },
    { -58,-38,-13,-28,-31,-27,-63,-99, -25,-8,-25,-2,-9,-25,-24,-52, -24,-20,10,9,-1,-9,-19,-41,
      -17,3,22,22,22,11,8,-18, -18,-6,16,25,16,17,4,-18, -23,-3,-1,15,10,-3,-20,-22,
      -42,-20,-10,-5,-2,-20,-23,-44, -29,-51,-23,-15,-22,-18,-50,-64 },
    { -14,-21,-11,-8,-7,-9,-17,-24, -8,-4,7,-12,-3,-13,-4,-14, 2,-8,0,-1,-2,6,0,4,
      -3,9,12,9,14,10,3,2, -6,3,13,19,7,10,-3,-9, -12,-3,8,10,13,3,-7,-15,
      -14,-18,-7,-1,4,-9,-15,-27, -23,-9,-23,-5,-9,-16,-5,-17 },
    { 13,10,18,15,12,12,8,5, 11,13,13,11,-3,3,8,3, 7,7,7,5,4,-3,-5,-3,
      4,3,13,1,2,1,-1,2, 3,5,8,4,-5,-6,-8,-11, -4,0,-5,-1,-7,-12,-8,-16,
      -6,-6,0,2,-9,-9,-11,-3, -9,2,3,-1,-5,-13,4,-20 },
    { -9,22,22,27,27,19,10,20, -17,20,32,41,58,25,30,0, -20,6,9,49,47,35,19,9,
      3,22,24,45,57,40,57,36, -18,28,19,47,31,34,39,23, -16,-27,15,6,9,17,10,5,
      -22,-23,-30,-16,-16,-23,-36,-32, -33,-28,-22,-43,-5,-32,-20,-41 },
    { -74,-35,-18,-18,-11,15,4,-17, -12,17,14,17,17,38,23,11, 10,17,23,15,20,45,44,13,
      -8,22,24,27,26,33,26,3, -18,-4,21,24,27,23,9,-11, -19,-3,11,21,23,16,7,-9,
      -27,-11,4,13,14,4,-5,-17, -53,-34,-21,-11,-28,-14,-24,-43 }
};
static const int MobKnightMG[9]  = {-25,-20,-14,-8,-2,4,10,16,20};
static const int MobKnightEG[9]  = {-30,-24,-16,-8,0,8,14,20,24};
static const int MobBishopMG[14] = {-20,-14,-8,-2,3,7,11,15,18,21,23,24,25,26};
static const int MobBishopEG[14] = {-25,-18,-10,-2,4,9,14,18,21,24,26,27,28,29};
static const int MobRookMG[15]   = {-18,-12,-6,-1,3,6,9,12,14,16,17,18,18,19,19};
static const int MobRookEG[15]   = {-22,-16,-8,-2,3,7,10,13,15,17,18,19,20,21,22};
static const int MobQueenMG[28]  = {-15,-10,-6,-2,1,4,6,8,10,11,12,13,14,15,16,17,18,18,19,19,20,20,21,21,22,22,23,23};
static const int MobQueenEG[28]  = {-20,-14,-8,-3,1,5,8,11,13,15,17,18,19,20,21,22,22,23,23,24,24,24,25,25,25,26,26,26};
static const int PassedMG[8] = {0, 5, 12, 25, 45, 78, 130, 0};
static const int PassedEG[8] = {0, 12, 25, 45, 80, 130, 200, 0};
static const int IsolMG = -14, IsolEG = -18;
static const int DoubledMG = -12, DoubledEG = -22;
static const int BishopPairMG = 30, BishopPairEG = 55;
static const int RookOpenMG = 25, RookOpenEG = 12;
static const int RookSemiMG = 12, RookSemiEG = 6;
static const int Rook7thMG = 22, Rook7thEG = 34;
static const int OutpostMG = 22, OutpostEG = 12;
static const int ThreatPawnMG = 55, ThreatPawnEG = 35;
static const int KingShield1 = 14, KingShield2 = 7, KingOpen = 18;

static int evaluate(const Position& pos) {
    int mg = 0, eg = 0, phase = 0;
    for (int c = 0; c < 2; c++) {
        Color us = Color(c), them = Color(c^1);
        int sign = (us == WHITE) ? 1 : -1;

        if (pos.kingSq[us] != NO_SQ) {
            int ksq = pos.kingSq[us];
            int kf = fileOf(ksq), kr = rankOf(ksq);
            int shield = 0;
            for (int df = -1; df <= 1; df++) {
                int f = kf + df;
                if (f < 0 || f > 7) continue;
                U64 fileBB = FILE_A << f;
                U64 ourPawns = pos.pieces[us][PAWN];
                if (!(ourPawns & fileBB)) { shield -= KingOpen; continue; }
                U64 pp = ourPawns & fileBB;
                int r = (us == WHITE) ? (msb(pp)>>3) : (lsb(pp)>>3);
                int dist = std::abs(r - kr);
                if (dist == 1) shield += KingShield1;
                else if (dist == 2) shield += KingShield2;
                else shield -= KingOpen;
            }
            mg += sign * shield;
        }

        if (popcnt(pos.pieces[us][BISHOP]) >= 2) {
            mg += sign * BishopPairMG; eg += sign * BishopPairEG;
        }

        for (int pt = 0; pt < 6; pt++) {
            U64 bb = pos.pieces[us][pt];
            while (bb) {
                int sq = poplsb(bb);
                int rel = (us == WHITE) ? sq : (sq ^ 56);
                int pmg = MatMG[pt] + PST_MG[pt][rel];
                int peg = MatEG[pt] + PST_EG[pt][rel];
                mg += sign * pmg; eg += sign * peg;
                phase += PhaseW[pt];

                if (pt != PAWN && pt != KING) {
                    U64 att = 0;
                    switch (pt) {
                        case KNIGHT: att = KnightAtt[sq]; break;
                        case BISHOP: att = bishopAtt(sq, pos.all); break;
                        case ROOK:   att = rookAtt(sq, pos.all);   break;
                        case QUEEN:  att = queenAtt(sq, pos.all);  break;
                    }
                    att &= ~pos.occ[us];
                    int mob = popcnt(att);
                    int mmg = 0, meg = 0;
                    switch (pt) {
                        case KNIGHT: if (mob>8) mob=8;  mmg=MobKnightMG[mob]; meg=MobKnightEG[mob]; break;
                        case BISHOP: if (mob>13) mob=13; mmg=MobBishopMG[mob]; meg=MobBishopEG[mob]; break;
                        case ROOK:   if (mob>14) mob=14; mmg=MobRookMG[mob];   meg=MobRookEG[mob];   break;
                        case QUEEN:  if (mob>27) mob=27; mmg=MobQueenMG[mob];  meg=MobQueenEG[mob];  break;
                    }
                    mg += sign * mmg; eg += sign * meg;

                    if (pt == ROOK) {
                        int f = fileOf(sq);
                        U64 fileBB = FILE_A << f;
                        if (!(pos.pieces[us][PAWN] & fileBB)) {
                            if (!(pos.pieces[them][PAWN] & fileBB)) { mg += sign*RookOpenMG; eg += sign*RookOpenEG; }
                            else { mg += sign*RookSemiMG; eg += sign*RookSemiEG; }
                        }
                        int r7 = (us==WHITE) ? 6 : 1;
                        if (rankOf(sq) == r7) { mg += sign*Rook7thMG; eg += sign*Rook7thEG; }
                    }

                    if (pt == KNIGHT) {
                        int rr = (us==WHITE) ? rankOf(sq) : 7-rankOf(sq);
                        if (rr >= 3 && rr <= 5) {
                            U64 att2 = PawnAtt[them][sq] & pos.pieces[us][PAWN];
                            if (att2) {
                                bool kick = false;
                                for (int df = -1; df <= 1; df += 2) {
                                    int f2 = fileOf(sq) + df;
                                    if (f2 < 0 || f2 > 7) continue;
                                    U64 ep = pos.pieces[them][PAWN] & (FILE_A << f2);
                                    if (ep) {
                                        int er = (us==WHITE) ? (lsb(ep)>>3) : (msb(ep)>>3);
                                        if (us==WHITE) { if (er > rankOf(sq)) kick = true; }
                                        else           { if (er < rankOf(sq)) kick = true; }
                                    }
                                }
                                if (!kick) { mg += sign*OutpostMG; eg += sign*OutpostEG; }
                            }
                        }
                    }
                }
            }
        }

        U64 pp = pos.pieces[us][PAWN];
        while (pp) {
            int sq = poplsb(pp);
            U64 att = PawnAtt[us][sq] & pos.occ[them];
            while (att) {
                int t = poplsb(att);
                Piece p = pieceOn(pos, Square(t));
                if (p == NO_PIECE) continue;
                PieceType pt = pcType(p);
                if (pt >= KNIGHT && pt <= QUEEN) { mg += sign*ThreatPawnMG; eg += sign*ThreatPawnEG; }
            }
        }
    }

    for (int c = 0; c < 2; c++) {
        Color us = Color(c), them = Color(c^1);
        int sign = (us==WHITE) ? 1 : -1;
        U64 ourPawns = pos.pieces[us][PAWN];
        U64 enemyPawns = pos.pieces[them][PAWN];
        U64 b = ourPawns;
        while (b) {
            int sq = poplsb(b);
            int f = fileOf(sq);
            U64 fileBB = FILE_A << f;
            U64 adj = 0;
            if (f>0) adj |= FILE_A << (f-1);
            if (f<7) adj |= FILE_A << (f+1);
            if (popcnt(ourPawns & fileBB) > 1) { mg += sign*(DoubledMG/2); eg += sign*(DoubledEG/2); }
            if (!(ourPawns & adj)) { mg += sign*IsolMG; eg += sign*IsolEG; }
            U64 ahead = (us==WHITE) ? (~((bit(sq)-1) | bit(sq))) : ((bit(sq)-1));
            if (!(enemyPawns & (fileBB | adj) & ahead)) {
                int rr = (us==WHITE) ? rankOf(sq) : 7-rankOf(sq);
                mg += sign*PassedMG[rr]; eg += sign*PassedEG[rr];
            }
        }
    }

    int ph = phase > 24 ? 24 : phase;
    int score = (mg*ph + eg*(24-ph)) / 24;
    return (pos.side == WHITE) ? score : -score;
}

// ---- TT ----
// [v3.4] 19 bits = 512K entries × 16 bytes = 8MB (better for phone cache)
static constexpr int TT_BITS = 19;
static constexpr int TT_SIZE = 1 << TT_BITS;
static constexpr int TT_MASK = TT_SIZE - 1;

enum TTFlag { TT_NONE=0, TT_EXACT=1, TT_LOWER=2, TT_UPPER=3 };

struct TTEntry {
    U64 key;        // 8
    int32_t score;  // 4
    Move move;      // 2
    int8_t depth;   // 1
    uint8_t flag;   // 1
};
static_assert(sizeof(TTEntry) == 16, "TTEntry must be 16 bytes");

static TTEntry TT[TT_SIZE];
static uint8_t ttGen = 0;
static void ttClear() { memset(TT, 0, sizeof(TT)); ttGen = 0; }

// ---- Search ----
static const int INF = 1000000;
static const int MATE = 100000;
static const int MAX_PLY = 128;

static int64_t nodes;
static bool stopped;
static std::chrono::steady_clock::time_point startTime;
static int64_t hardLimitMs, softLimitMs;
static bool g_silent = true;

static int killers[MAX_PLY][2];
static int32_t history[2][64][64];
static Move counterMoves[64][64];
static int checkExtStack[MAX_PLY];

static inline void checkTime() {
    if ((nodes & 511) == 0) {
        auto now = std::chrono::steady_clock::now();
        int64_t el = std::chrono::duration_cast<std::chrono::milliseconds>(now - startTime).count();
        if (el > hardLimitMs) stopped = true;
    }
}

static bool isRepetition(const Position& pos) {
    int lim = std::min(pos.halfmove, pos.histCount - 1);
    for (int i = pos.histCount-3; i >= 0 && i >= pos.histCount-1-lim; i -= 2)
        if (pos.histHash[i] == pos.hash) return true;
    return false;
}
static int countReps(const Position& pos) {
    int cnt = 1;
    int lim = std::min(pos.halfmove, pos.histCount - 1);
    for (int i = pos.histCount-3; i >= 0 && i >= pos.histCount-1-lim; i -= 2)
        if (pos.histHash[i] == pos.hash) cnt++;
    return cnt;
}
static bool hasNonPawn(const Position& pos, Color c) {
    return (pos.pieces[c][KNIGHT] | pos.pieces[c][BISHOP]
          | pos.pieces[c][ROOK]   | pos.pieces[c][QUEEN]) != 0;
}

static int quiesce(Position& pos, int alpha, int beta, int ply) {
    if (stopped) return 0;
    checkTime();
    nodes++;
    if (ply >= MAX_PLY - 1) return evaluate(pos);

    bool inChk = pos.inCheck(pos.side);
    int stand = -INF;
    MoveList ml;
    if (inChk) genMoves(pos, ml, false);
    else {
        stand = evaluate(pos);
        if (stand >= beta) return stand;
        if (stand > alpha) alpha = stand;
        genMoves(pos, ml, true);
    }

    int scores[256];
    for (int i = 0; i < ml.count; i++) {
        Move m = ml.moves[i];
        int to = mTo(m);
        int sc = 0;
        if (pos.all & bit(to)) {
            Piece p = pieceOn(pos, Square(to));
            if (p != NO_PIECE) sc = 100000 + PieceValue[pcType(p)] * 10;
        } else if (mFlag(m) == 2) sc = 100000 + PieceValue[PAWN]*10;
        else if (mPromo(m)) sc = 90000 + PieceValue[mPromo(m)];
        scores[i] = sc;
    }

    int best = inChk ? -INF : stand;
    int legal = 0;
    for (int i = 0; i < ml.count; i++) {
        int bi = i;
        for (int j = i+1; j < ml.count; j++) if (scores[j] > scores[bi]) bi = j;
        std::swap(ml.moves[i], ml.moves[bi]);
        std::swap(scores[i], scores[bi]);

        Move m = ml.moves[i];
        if (!inChk && scores[i] < 0) continue;
        if (!inChk && !seeGE(pos, m, 0)) continue;

        if (!inChk) {
            int to = mTo(m);
            int victimVal = 0;
            if (pos.all & bit(to)) {
                Piece p = pieceOn(pos, Square(to));
                if (p != NO_PIECE) victimVal = PieceValue[pcType(p)];
            } else if (mFlag(m) == 2) victimVal = PieceValue[PAWN];
            if (mPromo(m)) victimVal += PieceValue[mPromo(m)] - PieceValue[PAWN];
            if (stand + victimVal + 200 < alpha) continue;
        }

        UndoInfo u;
        makeMove(pos, m, u);
        Color us = Color(pos.side ^ 1);
        if (pos.inCheck(us)) { unmakeMove(pos, m, u); continue; }
        legal++;
        int score = -quiesce(pos, -beta, -alpha, ply+1);
        unmakeMove(pos, m, u);
        if (stopped) return 0;
        if (score > best) best = score;
        if (score > alpha) alpha = score;
        if (alpha >= beta) break;
    }
    if (inChk && legal == 0) return -MATE + ply;
    return best;
}

static void scoreMoves(Position& pos, MoveList& ml, int scores[], Move ttMove, int ply) {
    Move counter = MOVE_NONE;
    if (pos.lastMove != MOVE_NONE)
        counter = counterMoves[mFrom(pos.lastMove)][mTo(pos.lastMove)];
    for (int i = 0; i < ml.count; i++) {
        Move m = ml.moves[i];
        if (m == ttMove) { scores[i] = 10000000; continue; }
        int to = mTo(m);
        if (pos.all & bit(to)) {
            Piece p = pieceOn(pos, Square(to));
            if (p != NO_PIECE) {
                int victim = PieceValue[pcType(p)];
                Piece a = pieceOn(pos, Square(mFrom(m)));
                int attacker = a != NO_PIECE ? PieceValue[pcType(a)] : 0;
                if (!seeGE(pos, m, 0)) scores[i] = -50000 + victim*10;
                else                   scores[i] = 1000000 + victim*10 - attacker;
            } else scores[i] = 900000;
        } else if (mFlag(m) == 2) scores[i] = 1000000 + PieceValue[PAWN]*10;
        else if (mPromo(m)) scores[i] = 900000 + PieceValue[mPromo(m)];
        else if (m == killers[ply][0]) scores[i] = 800000;
        else if (m == killers[ply][1]) scores[i] = 790000;
        else if (m == counter) scores[i] = 780000;
        else scores[i] = history[pos.side][mFrom(m)][to];
    }
}

static int negamax(Position& pos, int depth, int alpha, int beta, int ply, bool allowNull) {
    if (stopped) return 0;
    checkTime();
    nodes++;

    bool inChk = pos.inCheck(pos.side);

    // [v3.4] Explicit init of checkExtStack[0] at root
    if (ply == 0) checkExtStack[0] = 0;

    if (ply > 0) {
        if (pos.halfmove >= 100) return 0;
        if (isRepetition(pos)) return 0;
        if (ply >= MAX_PLY - 1) return evaluate(pos);

        checkExtStack[ply] = checkExtStack[ply-1];
        if (inChk && checkExtStack[ply] < 6) {
            depth++;
            checkExtStack[ply]++;
        }
        if (alpha < -MATE + ply) alpha = -MATE + ply;
        if (beta > MATE - ply - 1) beta = MATE - ply - 1;
        if (alpha >= beta) return alpha;
    }

    bool isPv = (beta - alpha) > 1;
    if (depth <= 0) return quiesce(pos, alpha, beta, ply);

    // [v3.4] Prefetch TT entry
    int ttIdx = pos.hash & TT_MASK;
    __builtin_prefetch(&TT[ttIdx], 0, 0);   // 0 = read
    TTEntry& te = TT[ttIdx];
    Move ttMove = MOVE_NONE;
    if (te.key == pos.hash && te.flag != TT_NONE) {
        ttMove = te.move;
        if (ply > 0 && !isPv && te.depth >= depth) {
            int s = te.score;
            if (s > MATE - 1000) s -= ply;
            else if (s < -MATE + 1000) s += ply;
            if (te.flag == TT_EXACT) return s;
            if (te.flag == TT_LOWER && s >= beta) return s;
            if (te.flag == TT_UPPER && s <= alpha) return s;
        }
    }

    int staticEval = evaluate(pos);

    if (!isPv && !inChk && depth <= 3 && staticEval + 200 + 100*depth < alpha) {
        int v = quiesce(pos, alpha, beta, ply);
        if (v <= alpha) return v;
    }
    if (!isPv && !inChk && depth <= 4 && staticEval + 90*depth <= alpha
        && std::abs(alpha) < MATE - 1000) return staticEval;

    if (!isPv && !inChk && allowNull && depth >= 3 && ply > 0
        && staticEval >= beta && std::abs(beta) < MATE - 1000 && hasNonPawn(pos, pos.side)) {
        UndoInfo u;
        u.castling = pos.castling; u.ep = pos.ep; u.halfmove = pos.halfmove;
        u.fullmove = pos.fullmove; u.hash = pos.hash; u.captured = NO_PIECE;
        u.lastMove = pos.lastMove; u.histIdx = pos.histCount;
        if (pos.ep != NO_SQ) pos.hash ^= Zep[fileOf(pos.ep)];
        pos.ep = NO_SQ;
        pos.side = Color(pos.side ^ 1);
        pos.hash ^= Zside;
        pos.halfmove++;
        pos.lastMove = MOVE_NONE;
        if (pos.histCount < 1024) pos.histHash[pos.histCount++] = pos.hash;

        int R = 3 + depth/6;
        if (staticEval - beta > 200) R++;
        if (R > depth - 2) R = std::max(1, depth - 2);
        int score = -negamax(pos, depth - 1 - R, -beta, -beta+1, ply+1, false);

        pos.side = Color(pos.side ^ 1);
        pos.castling = u.castling; pos.ep = u.ep; pos.halfmove = u.halfmove;
        pos.fullmove = u.fullmove; pos.hash = u.hash;
        pos.lastMove = u.lastMove; pos.histCount = u.histIdx;

        if (stopped) return 0;
        if (score >= beta) return (score > MATE - 1000) ? beta : score;
    }

    if (isPv && ttMove == MOVE_NONE && depth >= 5) {
        negamax(pos, depth-2, alpha, beta, ply, false);
        if (te.key == pos.hash && te.flag != TT_NONE) ttMove = te.move;
    }

    MoveList ml;
    genMoves(pos, ml, false);
    int scores[256];
    scoreMoves(pos, ml, scores, ttMove, ply);

    int best = -INF, bestMove = MOVE_NONE, legal = 0;
    int origAlpha = alpha;
    int quietsTried = 0;

    for (int i = 0; i < ml.count; i++) {
        int bi = i;
        for (int j = i+1; j < ml.count; j++) if (scores[j] > scores[bi]) bi = j;
        std::swap(ml.moves[i], ml.moves[bi]);
        std::swap(scores[i], scores[bi]);

        Move m = ml.moves[i];
        int to = mTo(m);
        bool quiet = !(pos.all & bit(to)) && mFlag(m) != 2 && !mPromo(m);

        if (quiet) {
            quietsTried++;
            if (!isPv && !inChk && depth <= 3 && quietsTried > 4 + depth*depth) continue;
        }

        UndoInfo u;
        makeMove(pos, m, u);
        Color us = Color(pos.side ^ 1);
        if (pos.inCheck(us)) { unmakeMove(pos, m, u); continue; }
        legal++;

        int newDepth = depth - 1;
        int score;

        if (legal == 1) {
            score = -negamax(pos, newDepth, -beta, -alpha, ply+1, true);
        } else {
            int R = 0;
            if (depth >= 3 && legal > 3 && quiet && !inChk) {
                R = 1;
                if (legal > 6) R = 2;
                if (depth >= 6) R = 3;
                if (isPv) R--;
                if (R < 0) R = 0;
                if (R > newDepth - 2) R = std::max(0, newDepth - 2);
            }
            score = -negamax(pos, newDepth - R, -alpha-1, -alpha, ply+1, true);
            if (score > alpha && R > 0)
                score = -negamax(pos, newDepth, -alpha-1, -alpha, ply+1, true);
            if (score > alpha && score < beta)
                score = -negamax(pos, newDepth, -beta, -alpha, ply+1, true);
        }
        unmakeMove(pos, m, u);
        if (stopped) return 0;

        if (score > best) { best = score; bestMove = m; }
        if (score > alpha) {
            alpha = score;
            if (alpha >= beta) {
                if (quiet) {
                    if (killers[ply][0] != m) { killers[ply][1] = killers[ply][0]; killers[ply][0] = m; }
                    history[pos.side][mFrom(m)][to] += depth * depth;
                    if (history[pos.side][mFrom(m)][to] > 1000000) {
                        for (int a = 0; a < 2; a++)
                            for (int b = 0; b < 64; b++)
                                for (int cc = 0; cc < 64; cc++)
                                    history[a][b][cc] >>= 1;
                    }
                    if (pos.lastMove != MOVE_NONE)
                        counterMoves[mFrom(pos.lastMove)][mTo(pos.lastMove)] = m;
                }
                break;
            }
        }
    }

    if (legal == 0) return inChk ? (-MATE + ply) : 0;

    int flag = (best <= origAlpha) ? TT_UPPER : ((best >= beta) ? TT_LOWER : TT_EXACT);
    int storeScore = best;
    if (storeScore > MATE - 1000) storeScore += ply;
    else if (storeScore < -MATE + 1000) storeScore -= ply;
    if (te.key != pos.hash || depth >= te.depth || flag == TT_EXACT) {
        te.key = pos.hash;
        te.score = storeScore;
        te.move = bestMove;
        te.depth = (int8_t)depth;
        te.flag = (uint8_t)flag;
    }
    return best;
}

struct SearchResult { Move move; int score; int depth; int64_t nodes; int timeMs; };

static SearchResult search(Position& pos, int maxDepth, int64_t timeMs) {
    nodes = 0;
    stopped = false;
    startTime = std::chrono::steady_clock::now();
    hardLimitMs = timeMs > 0 ? timeMs : (int64_t)1e12;
    softLimitMs = hardLimitMs * 55 / 100;
    memset(killers, 0, sizeof(killers));
    memset(history, 0, sizeof(history));
    memset(counterMoves, 0, sizeof(counterMoves));
    memset(checkExtStack, 0, sizeof(checkExtStack));
    ttGen++;

    if (maxDepth > MAX_PLY - 5) maxDepth = MAX_PLY - 5;

    MoveList ml;
    genMoves(pos, ml);
    Move legalMoves[256];
    int nLegal = 0;
    for (int i = 0; i < ml.count; i++) {
        UndoInfo u;
        makeMove(pos, ml.moves[i], u);
        Color us = Color(pos.side ^ 1);
        if (!pos.inCheck(us)) legalMoves[nLegal++] = ml.moves[i];
        unmakeMove(pos, ml.moves[i], u);
    }
    if (nLegal == 0) return {MOVE_NONE, 0, 0, 0, 0};

    Move bestMove = legalMoves[0];
    int bestScore = 0, completedDepth = 0;
    int64_t lastNodes = 1;

    for (int d = 1; d <= maxDepth; d++) {
        int alpha = -INF, beta = INF;
        if (d >= 4 && std::abs(bestScore) < MATE - 1000) {
            alpha = bestScore - 35;
            beta  = bestScore + 35;
        }

        if (bestMove != MOVE_NONE) {
            for (int k = 0; k < nLegal; k++)
                if (legalMoves[k] == bestMove) { std::swap(legalMoves[0], legalMoves[k]); break; }
        }

        Move iterBest = MOVE_NONE;
        int iterScore = -INF;
        int guard = 0;

        while (guard++ < 8) {
            iterBest = MOVE_NONE;
            iterScore = -INF;
            int a = alpha;
            bool fail = false;
            bool firstMove = true;

            for (int i = 0; i < nLegal; i++) {
                Move m = legalMoves[i];
                UndoInfo u;
                makeMove(pos, m, u);
                Color us = Color(pos.side ^ 1);
                if (pos.inCheck(us)) { unmakeMove(pos, m, u); continue; }

                int score;
                if (firstMove) {
    score = -negamax(pos, d-1, -beta, -a, 1, true);   // ← 1 بدل 0
    firstMove = false;
} else {
                    score = -negamax(pos, d-1, -a-1, -a, 1, true);
                    if (score > a && score < beta)
                        score = -negamax(pos, d-1, -beta, -a, 1, true);
                }
                unmakeMove(pos, m, u);
                if (stopped) { fail = true; break; }

                if (score > iterScore) {
                    iterScore = score;
                    iterBest = m;
                    std::swap(legalMoves[0], legalMoves[i]);
                }
                if (score > a) a = score;
                if (a >= beta) break;
            }
            if (fail) break;
            if (iterScore <= alpha) { alpha = iterScore - 80; beta = (alpha+beta)/2; continue; }
            if (iterScore >= beta)  { beta = iterScore + 80; continue; }
            break;
        }
        if (stopped) break;

        bool bestChanged = (iterBest != MOVE_NONE && iterBest != bestMove);
        if (iterBest != MOVE_NONE) { bestMove = iterBest; bestScore = iterScore; }
        completedDepth = d;

        auto now = std::chrono::steady_clock::now();
        int64_t el = std::chrono::duration_cast<std::chrono::milliseconds>(now - startTime).count();

        if (!g_silent) {
            std::printf("info depth %d score cp %d nodes %lld time %lld pv %c%d%c%d\n",
                        d, bestScore, (long long)nodes, (long long)el,
                        'a'+fileOf(mFrom(bestMove)), 1+rankOf(mFrom(bestMove)),
                        'a'+fileOf(mTo(bestMove)),   1+rankOf(mTo(bestMove)));
            std::fflush(stdout);
        }

        if (std::abs(bestScore) > MATE - 1000) break;

        double stability = bestChanged ? 0.4 : 1.0;
        double factor = 1.0 + 0.4 * (1.0 - stability);
        int64_t alloc = (int64_t)(softLimitMs * factor);
        if (el > alloc) break;
        lastNodes = nodes;
    }

    auto now = std::chrono::steady_clock::now();
    int el = (int)std::chrono::duration_cast<std::chrono::milliseconds>(now - startTime).count();
    return {bestMove, bestScore, completedDepth, nodes, el};
}

// ---- Init ----
static bool g_initialized = false;
static void initAll() {
    if (g_initialized) return;
    initZobrist();
    initLeapers();
    initRays();
    ttClear();
    g_initialized = true;
}

// ---- WASM interface ----
#ifdef __EMSCRIPTEN__
#include <emscripten/emscripten.h>
#define EAPI EMSCRIPTEN_KEEPALIVE
#else
#define EAPI
#endif

static Position g_pos;
static SearchResult g_last;
static std::vector<Move> g_legal;
static std::vector<std::pair<Move, UndoInfo>> g_moveStack;

extern "C" {

EAPI void engine_init() {
    initAll();
    g_pos.setFen("rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1");
    g_last = {};
    g_moveStack.clear();
}

EAPI void engine_set_silent(int s) { g_silent = (s != 0); }

EAPI void engine_set_fen(const char* fen) {
    if (!g_initialized) initAll();
    g_pos.setFen(fen ? fen : "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1");
    g_moveStack.clear();
}

EAPI const char* engine_get_fen() {
    static std::string s;
    s = g_pos.toFen();
    return s.c_str();
}

EAPI int engine_search(int depth, int timeMs) {
    if (!g_initialized) initAll();
    if (depth < 1) depth = 1;
    if (depth > MAX_PLY - 5) depth = MAX_PLY - 5;
    g_last = search(g_pos, depth, (int64_t)timeMs);
    return (int)g_last.move;
}

EAPI int engine_get_score() { return g_last.score; }
EAPI int engine_get_depth() { return g_last.depth; }
EAPI int engine_get_nodes() { return (int)g_last.nodes; }
EAPI int engine_get_time()  { return g_last.timeMs; }
EAPI int engine_get_side()  { return g_pos.side; }
EAPI int engine_in_check()  { return g_pos.inCheck(g_pos.side) ? 1 : 0; }
EAPI int engine_get_halfmove() { return g_pos.halfmove; }

EAPI int engine_gen_legal() {
    g_legal.clear();
    MoveList ml;
    genMoves(g_pos, ml);
    for (int i = 0; i < ml.count; i++) {
        UndoInfo u;
        makeMove(g_pos, ml.moves[i], u);
        Color us = Color(g_pos.side ^ 1);
        if (!g_pos.inCheck(us)) g_legal.push_back(ml.moves[i]);
        unmakeMove(g_pos, ml.moves[i], u);
    }
    return (int)g_legal.size();
}
EAPI int engine_get_legal(int i) {
    if (i < 0 || i >= (int)g_legal.size()) return 0;
    return g_legal[i];
}
EAPI void engine_make(int m) {
    UndoInfo u;
    makeMove(g_pos, Move(m), u);
    g_moveStack.push_back({Move(m), u});
}
EAPI int engine_unmake() {
    if (g_moveStack.empty()) return 0;
    auto p = g_moveStack.back();
    g_moveStack.pop_back();
    unmakeMove(g_pos, p.first, p.second);
    return 1;
}
EAPI int engine_move_from(int m) { return mFrom(Move(m)); }
EAPI int engine_move_to(int m)   { return mTo(Move(m)); }
EAPI int engine_move_promo(int m){ return mPromo(Move(m)); }

EAPI int engine_game_status() {
    MoveList ml;
    genMoves(g_pos, ml);
    int legal = 0;
    for (int i = 0; i < ml.count; i++) {
        UndoInfo u;
        makeMove(g_pos, ml.moves[i], u);
        Color us = Color(g_pos.side ^ 1);
        if (!g_pos.inCheck(us)) legal++;
        unmakeMove(g_pos, ml.moves[i], u);
    }
    if (legal == 0) return g_pos.inCheck(g_pos.side) ? 1 : 2;
    if (g_pos.halfmove >= 100) return 3;
    if (countReps(g_pos) >= 3) return 4;
    return 0;
}

static std::chrono::steady_clock::time_point perftStart;
static int64_t perftCounter;

static int64_t perftImpl(Position& pos, int depth) {
    if ((++perftCounter & 0x3FFF) == 0) {
        auto now = std::chrono::steady_clock::now();
        int64_t el = std::chrono::duration_cast<std::chrono::milliseconds>(now - perftStart).count();
        if (el > 30000) return -1;
    }
    if (depth == 0) return 1;
    MoveList ml;
    genMoves(pos, ml);
    int64_t total = 0;
    for (int i = 0; i < ml.count; i++) {
        UndoInfo u;
        makeMove(pos, ml.moves[i], u);
        Color us = Color(pos.side ^ 1);
        if (!pos.inCheck(us)) {
            int64_t sub = perftImpl(pos, depth-1);
            unmakeMove(pos, ml.moves[i], u);
            if (sub < 0) return -1;
            total += sub;
        } else unmakeMove(pos, ml.moves[i], u);
    }
    return total;
}

EAPI int64_t engine_perft(int depth) {
    if (depth < 1) return 0;
    perftStart = std::chrono::steady_clock::now();
    perftCounter = 0;
    Position copy = g_pos;
    return perftImpl(copy, depth);
}

} // extern "C"

// ---- UCI ----
#ifndef __EMSCRIPTEN__
// [v3.4] Full UCI "position ... moves ..." support
static bool parseAndApplyMove(const std::string& s, size_t& pos) {
    // expects: e2e4  or  e7e8q
    if (pos + 3 >= s.size()) return false;
    int f1 = s[pos] - 'a', r1 = s[pos+1] - '1';
    int f2 = s[pos+2] - 'a', r2 = s[pos+3] - '1';
    if (f1 < 0 || f1 > 7 || r1 < 0 || r1 > 7 ||
        f2 < 0 || f2 > 7 || r2 < 0 || r2 > 7) return false;
    int promo = 0;
    size_t adv = 4;
    if (pos + 4 < s.size()) {
        char pc = s[pos+4];
        if (pc == 'n') { promo = KNIGHT; adv = 5; }
        else if (pc == 'b') { promo = BISHOP; adv = 5; }
        else if (pc == 'r') { promo = ROOK; adv = 5; }
        else if (pc == 'q') { promo = QUEEN; adv = 5; }
    }
    int fromSq = mkSq(f1, r1), toSq = mkSq(f2, r2);

    MoveList ml;
    genMoves(g_pos, ml);
    Move chosen = MOVE_NONE;
    for (int i = 0; i < ml.count; i++) {
        Move m = ml.moves[i];
        if (mFrom(m) != fromSq || mTo(m) != toSq) continue;
        if (promo != 0 && mPromo(m) != promo) continue;
        UndoInfo u;
        makeMove(g_pos, m, u);
        Color us = Color(g_pos.side ^ 1);
        bool legal = !g_pos.inCheck(us);
        unmakeMove(g_pos, m, u);
        if (legal) { chosen = m; break; }
    }
    if (chosen == MOVE_NONE) return false;
    UndoInfo u;
    makeMove(g_pos, chosen, u);
    pos += adv;
    return true;
}

int main() {
    g_silent = false;
    initAll();
    g_pos.setFen("rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1");
    std::string line;
    while (std::getline(std::cin, line)) {
        if (line == "uci") { printf("id name BitEngine 3.4\nid author You\nuciok\n"); fflush(stdout); }
        else if (line == "isready") { printf("readyok\n"); fflush(stdout); }
        else if (line == "ucinewgame") { ttClear(); }
        else if (line.substr(0, 8) == "position") {
            // 1) Setup position
            if (line.find("startpos") != std::string::npos)
                g_pos.setFen("rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1");
            else {
                size_t fp = line.find("fen");
                if (fp != std::string::npos) {
                    size_t mp = line.find("moves");
                    std::string fen = line.substr(fp + 4,
                        (mp == std::string::npos ? line.size() : mp) - (fp + 4));
                    g_pos.setFen(fen);
                }
            }
            // 2) Apply moves if any
            size_t mp = line.find("moves");
            if (mp != std::string::npos) {
                size_t i = mp + 6;
                while (i < line.size()) {
                    while (i < line.size() && line[i] == ' ') i++;
                    if (i >= line.size()) break;
                    if (!parseAndApplyMove(line, i)) break;
                }
            }
        } else if (line.substr(0, 2) == "go") {
            int depth = 64; long long mt = 3000;
            if (line.find("movetime") != std::string::npos) sscanf(line.c_str(), "go movetime %lld", &mt);
            if (line.find("depth") != std::string::npos) sscanf(line.c_str(), "go depth %d", &depth);
            SearchResult r = search(g_pos, depth, mt);
            printf("bestmove %c%d%c%d",
                   'a'+fileOf(mFrom(r.move)), 1+rankOf(mFrom(r.move)),
                   'a'+fileOf(mTo(r.move)),   1+rankOf(mTo(r.move)));
            if (mPromo(r.move)) printf("%c", "  nbrq"[mPromo(r.move)]);
            printf("\n"); fflush(stdout);
        } else if (line.substr(0, 5) == "perft") {
            int d = 4; sscanf(line.c_str(), "perft %d", &d);
            perftStart = std::chrono::steady_clock::now();
            perftCounter = 0;
            Position copy = g_pos;
            int64_t n = perftImpl(copy, d);
            auto now = std::chrono::steady_clock::now();
            int64_t el = std::chrono::duration_cast<std::chrono::milliseconds>(now - perftStart).count();
            printf("perft %d = %lld  time %lld ms\n", d, (long long)n, (long long)el);
            fflush(stdout);
        } else if (line == "quit") break;
    }
    return 0;
}
#endif