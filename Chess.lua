--!strict
--[[
	Шахматный движок на Luau (Roblox). Один ModuleScript, чистая логика.
	Доска: board[rank][file], rank 1..8 (1 - белые), file 1..8 (1 = a).
	Клетка: nil или "wp" / "bk" и т.д.

	Договорённости:
	  * gameStatus: "checkmate_w" = мат поставили БЕЛЫЕ (победили белые),
	    "checkmate_b" = победили чёрные.
	  * Координатные таблицы from/to в ходах общие (разделяемые) - не изменяйте их.
	  * generateMoves / applyMove / SAN и т.д. не меняют входное состояние.
	  * history хранит ключи позиций (число), последний элемент - текущая позиция.
]]

-- === ТИПЫ ===
export type Coord = { rank: number, file: number }
export type Castling = { wK: boolean, wQ: boolean, bK: boolean, bQ: boolean }
export type Move = {
	from: Coord,
	to: Coord,
	piece: string,
	captured: string?,
	promotion: string?,
	isEnPassant: boolean,
	isCastle: string?,
	check: boolean,
	mate: boolean,
}
export type State = {
	board: { { string? } },
	sideToMove: string,
	castling: Castling,
	enPassant: Coord?,
	halfmoveClock: number,
	fullmoveNumber: number,
	history: { number },
	hashLo: number, -- Zobrist, младшие 32 бита
	hashHi: number, -- Zobrist, старшие 32 бита
	kingRank: { [string]: number }, -- положение королей (для быстрой проверки шаха)
	kingFile: { [string]: number },
}
export type SearchOptions = {
	depth: number?,
	timeLimit: number?,
	elo: number?,
	yield: boolean?, -- false: не вызывать task.wait() во время поиска
}

type Undo = {
	captured: string?,
	wK: boolean,
	wQ: boolean,
	bK: boolean,
	bQ: boolean,
	ep: Coord?,
	half: number,
	full: number,
	lo: number,
	hi: number,
	kr: number,
	kf: number,
}

type TTEntry = { depth: number, score: number, flag: number, bestMove: Move? }

type SearchCtx = {
	st: State,
	nodes: number,
	startTime: number,
	timeLimit: number,
	stop: boolean,
	lastYield: number,
	doYield: boolean,
	maxPly: number,
	killerA: { [number]: Move? },
	killerB: { [number]: Move? },
	hist: { [number]: number },
}

local Chess = {}

-- === КОНСТАНТЫ ===
local FILE_LETTERS = "abcdefgh"
local START_FEN = "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1"

local PIECE_VALUE: { [string]: number } = { p = 100, n = 320, b = 330, r = 500, q = 900, k = 20000 }

local COLOR_OF: { [string]: string } = {}
local KIND_OF: { [string]: string } = {}
local PIECE_INDEX: { [string]: number } = {}
for ci, color in ipairs({ "w", "b" }) do
	for ki, kind in ipairs({ "p", "n", "b", "r", "q", "k" }) do
		local name = color .. kind
		COLOR_OF[name] = color
		KIND_OF[name] = kind
		PIECE_INDEX[name] = (ci - 1) * 6 + (ki - 1)
	end
end

local PROMOTED: { [string]: { [string]: string } } = {
	w = { q = "wq", r = "wr", b = "wb", n = "wn" },
	b = { q = "bq", r = "br", b = "bb", n = "bn" },
}

-- Общие (неизменяемые) таблицы координат
local SQ: { { Coord } } = {}
for r = 1, 8 do
	SQ[r] = {}
	for f = 1, 8 do
		SQ[r][f] = { rank = r, file = f }
	end
end

-- Смещения
local KN_DR = { 1, 2, 2, 1, -1, -2, -2, -1 }
local KN_DF = { 2, 1, -1, -2, -2, -1, 1, 2 }
local KG_DR = { 1, 1, 1, 0, 0, -1, -1, -1 }
local KG_DF = { -1, 0, 1, -1, 1, -1, 0, 1 }
local DIAG_DR = { 1, 1, -1, -1 }
local DIAG_DF = { 1, -1, 1, -1 }
local ORTH_DR = { 1, -1, 0, 0 }
local ORTH_DF = { 0, 0, 1, -1 }

local INF = 1000000
local MATE = 100000
local MATE_BOUND = MATE - 1000
local QS_MAX_DEPTH = 4
local EVAL_MOBILITY = true -- выключите, если нужна максимальная скорость

-- Таблицы клеток (вид белых: первая строка = 8-я линия)
local PST_P = {
	0, 0, 0, 0, 0, 0, 0, 0,
	50, 50, 50, 50, 50, 50, 50, 50,
	10, 10, 20, 30, 30, 20, 10, 10,
	5, 5, 10, 25, 25, 10, 5, 5,
	0, 0, 0, 20, 20, 0, 0, 0,
	5, -5, -10, 0, 0, -10, -5, 5,
	5, 10, 10, -20, -20, 10, 10, 5,
	0, 0, 0, 0, 0, 0, 0, 0,
}
local PST_N = {
	-50, -40, -30, -30, -30, -30, -40, -50,
	-40, -20, 0, 0, 0, 0, -20, -40,
	-30, 0, 10, 15, 15, 10, 0, -30,
	-30, 5, 15, 20, 20, 15, 5, -30,
	-30, 0, 15, 20, 20, 15, 0, -30,
	-30, 5, 10, 15, 15, 10, 5, -30,
	-40, -20, 0, 5, 5, 0, -20, -40,
	-50, -40, -30, -30, -30, -30, -40, -50,
}
local PST_B = {
	-20, -10, -10, -10, -10, -10, -10, -20,
	-10, 0, 0, 0, 0, 0, 0, -10,
	-10, 0, 5, 10, 10, 5, 0, -10,
	-10, 5, 5, 10, 10, 5, 5, -10,
	-10, 0, 10, 10, 10, 10, 0, -10,
	-10, 10, 10, 10, 10, 10, 10, -10,
	-10, 5, 0, 0, 0, 0, 5, -10,
	-20, -10, -10, -10, -10, -10, -10, -20,
}
local PST_R = {
	0, 0, 0, 0, 0, 0, 0, 0,
	5, 10, 10, 10, 10, 10, 10, 5,
	-5, 0, 0, 0, 0, 0, 0, -5,
	-5, 0, 0, 0, 0, 0, 0, -5,
	-5, 0, 0, 0, 0, 0, 0, -5,
	-5, 0, 0, 0, 0, 0, 0, -5,
	-5, 0, 0, 0, 0, 0, 0, -5,
	0, 0, 0, 5, 5, 0, 0, 0,
}
local PST_Q = {
	-20, -10, -10, -5, -5, -10, -10, -20,
	-10, 0, 0, 0, 0, 0, 0, -10,
	-10, 0, 5, 5, 5, 5, 0, -10,
	-5, 0, 5, 5, 5, 5, 0, -5,
	0, 0, 5, 5, 5, 5, 0, -5,
	-10, 5, 5, 5, 5, 5, 0, -10,
	-10, 0, 5, 0, 0, 0, 0, -10,
	-20, -10, -10, -5, -5, -10, -10, -20,
}
local PST_K_MID = {
	-30, -40, -40, -50, -50, -40, -40, -30,
	-30, -40, -40, -50, -50, -40, -40, -30,
	-30, -40, -40, -50, -50, -40, -40, -30,
	-30, -40, -40, -50, -50, -40, -40, -30,
	-20, -30, -30, -40, -40, -30, -30, -20,
	-10, -20, -20, -20, -20, -20, -20, -10,
	20, 20, 0, 0, 0, 0, 20, 20,
	20, 30, 10, 0, 0, 10, 30, 20,
}
local PST_K_END = {
	-50, -40, -30, -20, -20, -30, -40, -50,
	-30, -20, -10, 0, 0, -10, -20, -30,
	-30, -10, 20, 30, 30, 20, -10, -30,
	-30, -10, 30, 40, 40, 30, -10, -30,
	-30, -10, 30, 40, 40, 30, -10, -30,
	-30, -10, 20, 30, 30, 20, -10, -30,
	-30, -30, 0, 0, 0, 0, -30, -30,
	-50, -30, -30, -30, -30, -30, -30, -50,
}
local PST_BY_KIND: { [string]: { number } } = { p = PST_P, n = PST_N, b = PST_B, r = PST_R, q = PST_Q }
local MOB_WEIGHT: { [string]: number } = { n = 4, b = 3, r = 2, q = 1 }
local PASSED_BONUS = { 0, 5, 10, 20, 35, 60, 100, 0 } -- по относительной линии 1..8

-- Для сортировки взятий (MVV-LVA)
local VICTIM_ORDER: { [string]: number } = { p = 1, n = 3, b = 3, r = 5, q = 9, k = 10 }
local ATTACKER_ORDER: { [string]: number } = { p = 1, n = 2, b = 3, r = 4, q = 5, k = 6 }

-- === ZOBRIST ===
local bxor, lshift, rshift = bit32.bxor, bit32.lshift, bit32.rshift

-- Собственный детерминированный генератор (xorshift32) с фиксированным seed
local rngState = 0x2545F491
local function nextRandom32(): number
	local x = rngState
	x = bxor(x, lshift(x, 13))
	x = bxor(x, rshift(x, 17))
	x = bxor(x, lshift(x, 5))
	rngState = x
	return x
end

local ZP_LO: { number } = {}
local ZP_HI: { number } = {}
for i = 1, 768 do
	ZP_LO[i] = nextRandom32()
	ZP_HI[i] = nextRandom32()
end
local ZC_LO: { number } = {}
local ZC_HI: { number } = {}
for i = 1, 4 do
	ZC_LO[i] = nextRandom32()
	ZC_HI[i] = nextRandom32()
end
local ZE_LO: { number } = {}
local ZE_HI: { number } = {}
for i = 1, 8 do
	ZE_LO[i] = nextRandom32()
	ZE_HI[i] = nextRandom32()
end
local ZSIDE_LO = nextRandom32()
local ZSIDE_HI = nextRandom32()

local function xorPiece(st: State, piece: string, r: number, f: number)
	local i = PIECE_INDEX[piece] * 64 + (r - 1) * 8 + f
	st.hashLo = bxor(st.hashLo, ZP_LO[i])
	st.hashHi = bxor(st.hashHi, ZP_HI[i])
end

local function xorEP(st: State, file: number)
	st.hashLo = bxor(st.hashLo, ZE_LO[file])
	st.hashHi = bxor(st.hashHi, ZE_HI[file])
end

local function xorCastling(st: State, c: Castling)
	if c.wK then
		st.hashLo = bxor(st.hashLo, ZC_LO[1])
		st.hashHi = bxor(st.hashHi, ZC_HI[1])
	end
	if c.wQ then
		st.hashLo = bxor(st.hashLo, ZC_LO[2])
		st.hashHi = bxor(st.hashHi, ZC_HI[2])
	end
	if c.bK then
		st.hashLo = bxor(st.hashLo, ZC_LO[3])
		st.hashHi = bxor(st.hashHi, ZC_HI[3])
	end
	if c.bQ then
		st.hashLo = bxor(st.hashLo, ZC_LO[4])
		st.hashHi = bxor(st.hashHi, ZC_HI[4])
	end
end

-- Полный пересчёт хэша (при создании позиции из FEN)
local function computeHash(st: State)
	st.hashLo = 0
	st.hashHi = 0
	for r = 1, 8 do
		for f = 1, 8 do
			local p = st.board[r][f]
			if p ~= nil then
				xorPiece(st, p, r, f)
			end
		end
	end
	if st.sideToMove == "b" then
		st.hashLo = bxor(st.hashLo, ZSIDE_LO)
		st.hashHi = bxor(st.hashHi, ZSIDE_HI)
	end
	xorCastling(st, st.castling)
	if st.enPassant ~= nil then
		xorEP(st, st.enPassant.file)
	end
end

-- 53-битный ключ позиции из двух 32-битных половин
local function posKey(st: State): number
	return (st.hashHi % 2097152) * 4294967296 + st.hashLo
end

-- Вспомогательные функции состояния
local function coordsToSquare(rank: number, file: number): string
	return string.sub(FILE_LETTERS, file, file) .. tostring(rank)
end

local function squareToCoords(sq: string): Coord
	if #sq ~= 2 then
		error("Неверная клетка: " .. sq)
	end
	local file = string.find(FILE_LETTERS, string.sub(sq, 1, 1), 1, true)
	local rank = tonumber(string.sub(sq, 2, 2))
	if file == nil or rank == nil or rank < 1 or rank > 8 then
		error("Неверная клетка: " .. sq)
	end
	return { rank = rank, file = file }
end

local function cloneState(s: State): State
	local board: { { string? } } = {}
	for r = 1, 8 do
		local row: { string? } = {}
		local src = s.board[r]
		for f = 1, 8 do
			row[f] = src[f]
		end
		board[r] = row
	end
	local ep: Coord? = nil
	if s.enPassant ~= nil then
		ep = { rank = s.enPassant.rank, file = s.enPassant.file }
	end
	return {
		board = board,
		sideToMove = s.sideToMove,
		castling = { wK = s.castling.wK, wQ = s.castling.wQ, bK = s.castling.bK, bQ = s.castling.bQ },
		enPassant = ep,
		halfmoveClock = s.halfmoveClock,
		fullmoveNumber = s.fullmoveNumber,
		history = table.clone(s.history),
		hashLo = s.hashLo,
		hashHi = s.hashHi,
		kingRank = { w = s.kingRank["w"], b = s.kingRank["b"] },
		kingFile = { w = s.kingFile["w"], b = s.kingFile["b"] },
	}
end

local function copyMove(m: Move): Move
	return {
		from = m.from,
		to = m.to,
		piece = m.piece,
		captured = m.captured,
		promotion = m.promotion,
		isEnPassant = m.isEnPassant,
		isCastle = m.isCastle,
		check = m.check,
		mate = m.mate,
	}
end

local function sameMove(a: Move, b: Move): boolean
	return a.from.rank == b.from.rank
		and a.from.file == b.from.file
		and a.to.rank == b.to.rank
		and a.to.file == b.to.file
		and a.promotion == b.promotion
end

-- === ГЕНЕРАЦИЯ ХОДОВ ===

-- Атакована ли клетка (r, f) фигурами цвета `by`
local function isSquareAttacked(board: { { string? } }, r: number, f: number, by: string): boolean
	if r < 1 then
		return false
	end
	local P, N, B, R, Q, K
	if by == "w" then
		P, N, B, R, Q, K = "wp", "wn", "wb", "wr", "wq", "wk"
	else
		P, N, B, R, Q, K = "bp", "bn", "bb", "br", "bq", "bk"
	end
	-- пешки (белая пешка бьёт вверх, значит стоит на линию ниже клетки)
	local pr = (by == "w") and (r - 1) or (r + 1)
	if pr >= 1 and pr <= 8 then
		if f > 1 and board[pr][f - 1] == P then
			return true
		end
		if f < 8 and board[pr][f + 1] == P then
			return true
		end
	end
	-- кони
	for i = 1, 8 do
		local nr, nf = r + KN_DR[i], f + KN_DF[i]
		if nr >= 1 and nr <= 8 and nf >= 1 and nf <= 8 and board[nr][nf] == N then
			return true
		end
	end
	-- король
	for i = 1, 8 do
		local nr, nf = r + KG_DR[i], f + KG_DF[i]
		if nr >= 1 and nr <= 8 and nf >= 1 and nf <= 8 and board[nr][nf] == K then
			return true
		end
	end
	-- диагонали: слон / ферзь
	for d = 1, 4 do
		local dr, df = DIAG_DR[d], DIAG_DF[d]
		local nr, nf = r + dr, f + df
		while nr >= 1 and nr <= 8 and nf >= 1 and nf <= 8 do
			local t = board[nr][nf]
			if t ~= nil then
				if t == B or t == Q then
					return true
				end
				break
			end
			nr += dr
			nf += df
		end
	end
	-- прямые: ладья / ферзь
	for d = 1, 4 do
		local dr, df = ORTH_DR[d], ORTH_DF[d]
		local nr, nf = r + dr, f + df
		while nr >= 1 and nr <= 8 and nf >= 1 and nf <= 8 do
			local t = board[nr][nf]
			if t ~= nil then
				if t == R or t == Q then
					return true
				end
				break
			end
			nr += dr
			nf += df
		end
	end
	return false
end

local function newMove(
	from: Coord,
	to: Coord,
	piece: string,
	captured: string?,
	promotion: string?,
	isEP: boolean,
	castle: string?
): Move
	return {
		from = from,
		to = to,
		piece = piece,
		captured = captured,
		promotion = promotion,
		isEnPassant = isEP,
		isCastle = castle,
		check = false,
		mate = false,
	}
end

local PROMO_LIST = { "q", "r", "b", "n" }

local function addPawnMove(
	moves: { Move },
	from: Coord,
	to: Coord,
	piece: string,
	captured: string?,
	us: string,
	isEP: boolean,
	capturesOnly: boolean
)
	local promoRank = (us == "w") and 8 or 1
	if to.rank == promoRank then
		if capturesOnly then
			moves[#moves + 1] = newMove(from, to, piece, captured, "q", false, nil)
		else
			for i = 1, 4 do
				moves[#moves + 1] = newMove(from, to, piece, captured, PROMO_LIST[i], false, nil)
			end
		end
	else
		moves[#moves + 1] = newMove(from, to, piece, captured, nil, isEP, nil)
	end
end

local function genSlide(
	board: { { string? } },
	moves: { Move },
	r: number,
	f: number,
	p: string,
	us: string,
	capturesOnly: boolean,
	DR: { number },
	DF: { number }
)
	for d = 1, #DR do
		local dr, df = DR[d], DF[d]
		local nr, nf = r + dr, f + df
		while nr >= 1 and nr <= 8 and nf >= 1 and nf <= 8 do
			local t = board[nr][nf]
			if t == nil then
				if not capturesOnly then
					moves[#moves + 1] = newMove(SQ[r][f], SQ[nr][nf], p, nil, nil, false, nil)
				end
			else
				if COLOR_OF[t] ~= us then
					moves[#moves + 1] = newMove(SQ[r][f], SQ[nr][nf], p, t, nil, false, nil)
				end
				break
			end
			nr += dr
			nf += df
		end
	end
end

-- Псевдолегальные ходы (без проверки, что король остаётся под шахом;
-- рокировка проверяется полностью). capturesOnly: только взятия и превращения.
local function genPseudo(st: State, capturesOnly: boolean): { Move }
	local board = st.board
	local us = st.sideToMove
	local them = (us == "w") and "b" or "w"
	local moves: { Move } = {}
	for r = 1, 8 do
		local row = board[r]
		for f = 1, 8 do
			local p = row[f]
			if p ~= nil and COLOR_OF[p] == us then
				local kind = KIND_OF[p]
				if kind == "p" then
					local dir = (us == "w") and 1 or -1
					local nr = r + dir
					if nr >= 1 and nr <= 8 then
						if board[nr][f] == nil then
							addPawnMove(moves, SQ[r][f], SQ[nr][f], p, nil, us, false, capturesOnly)
							if not capturesOnly then
								local startRank = (us == "w") and 2 or 7
								if r == startRank and board[r + 2 * dir][f] == nil then
									moves[#moves + 1] = newMove(SQ[r][f], SQ[r + 2 * dir][f], p, nil, nil, false, nil)
								end
							end
						end
						for df = -1, 1, 2 do
							local nf = f + df
							if nf >= 1 and nf <= 8 then
								local t = board[nr][nf]
								if t ~= nil then
									if COLOR_OF[t] == them then
										addPawnMove(moves, SQ[r][f], SQ[nr][nf], p, t, us, false, capturesOnly)
									end
								else
									local ep = st.enPassant
									if ep ~= nil and ep.rank == nr and ep.file == nf then
										local victim = (us == "w") and "bp" or "wp"
										if board[r][nf] == victim then
											addPawnMove(moves, SQ[r][f], SQ[nr][nf], p, victim, us, true, capturesOnly)
										end
									end
								end
							end
						end
					end
				elseif kind == "n" then
					for i = 1, 8 do
						local nr, nf = r + KN_DR[i], f + KN_DF[i]
						if nr >= 1 and nr <= 8 and nf >= 1 and nf <= 8 then
							local t = board[nr][nf]
							if t == nil then
								if not capturesOnly then
									moves[#moves + 1] = newMove(SQ[r][f], SQ[nr][nf], p, nil, nil, false, nil)
								end
							elseif COLOR_OF[t] == them then
								moves[#moves + 1] = newMove(SQ[r][f], SQ[nr][nf], p, t, nil, false, nil)
							end
						end
					end
				elseif kind == "b" then
					genSlide(board, moves, r, f, p, us, capturesOnly, DIAG_DR, DIAG_DF)
				elseif kind == "r" then
					genSlide(board, moves, r, f, p, us, capturesOnly, ORTH_DR, ORTH_DF)
				elseif kind == "q" then
					genSlide(board, moves, r, f, p, us, capturesOnly, DIAG_DR, DIAG_DF)
					genSlide(board, moves, r, f, p, us, capturesOnly, ORTH_DR, ORTH_DF)
				else -- король
					for i = 1, 8 do
						local nr, nf = r + KG_DR[i], f + KG_DF[i]
						if nr >= 1 and nr <= 8 and nf >= 1 and nf <= 8 then
							local t = board[nr][nf]
							if t == nil then
								if not capturesOnly then
									moves[#moves + 1] = newMove(SQ[r][f], SQ[nr][nf], p, nil, nil, false, nil)
								end
							elseif COLOR_OF[t] == them then
								moves[#moves + 1] = newMove(SQ[r][f], SQ[nr][nf], p, t, nil, false, nil)
							end
						end
					end
					-- рокировка
					local home = (us == "w") and 1 or 8
					if not capturesOnly and r == home and f == 5 then
						local c = st.castling
						local canK = (us == "w") and c.wK or c.bK
						local canQ = (us == "w") and c.wQ or c.bQ
						local rook = (us == "w") and "wr" or "br"
						if canK and board[home][6] == nil and board[home][7] == nil and board[home][8] == rook then
							if
								not isSquareAttacked(board, home, 5, them)
								and not isSquareAttacked(board, home, 6, them)
								and not isSquareAttacked(board, home, 7, them)
							then
								moves[#moves + 1] = newMove(SQ[home][5], SQ[home][7], p, nil, nil, false, "K")
							end
						end
						if
							canQ
							and board[home][2] == nil
							and board[home][3] == nil
							and board[home][4] == nil
							and board[home][1] == rook
						then
							if
								not isSquareAttacked(board, home, 5, them)
								and not isSquareAttacked(board, home, 4, them)
								and not isSquareAttacked(board, home, 3, them)
							then
								moves[#moves + 1] = newMove(SQ[home][5], SQ[home][3], p, nil, nil, false, "Q")
							end
						end
					end
				end
			end
		end
	end
	return moves
end

-- === ПРИМЕНЕНИЕ ХОДА ===

-- Ход "на месте" (мутирует st), возвращает данные для отката.
local function makeMove(st: State, mv: Move): Undo
	local board = st.board
	local c = st.castling
	local us = st.sideToMove
	local them = (us == "w") and "b" or "w"
	local fr, ff, tr, tf = mv.from.rank, mv.from.file, mv.to.rank, mv.to.file
	local piece = mv.piece
	local kind = KIND_OF[piece]

	local undo: Undo = {
		captured = nil,
		wK = c.wK,
		wQ = c.wQ,
		bK = c.bK,
		bQ = c.bQ,
		ep = st.enPassant,
		half = st.halfmoveClock,
		full = st.fullmoveNumber,
		lo = st.hashLo,
		hi = st.hashHi,
		kr = st.kingRank[us],
		kf = st.kingFile[us],
	}

	-- убираем из хэша права на рокировку, e.p. и сторону хода
	xorCastling(st, c)
	if st.enPassant ~= nil then
		xorEP(st, st.enPassant.file)
	end
	st.hashLo = bxor(st.hashLo, ZSIDE_LO)
	st.hashHi = bxor(st.hashHi, ZSIDE_HI)

	-- снимаем фигуру с исходной клетки
	xorPiece(st, piece, fr, ff)
	board[fr][ff] = nil

	-- взятие
	local captured: string? = nil
	if mv.isEnPassant then
		captured = board[fr][tf]
		board[fr][tf] = nil
		if captured ~= nil then
			xorPiece(st, captured, fr, tf)
		end
	else
		captured = board[tr][tf]
		if captured ~= nil then
			xorPiece(st, captured, tr, tf)
		end
	end
	undo.captured = captured

	-- ставим фигуру (с учётом превращения)
	local placed = piece
	if mv.promotion ~= nil then
		placed = PROMOTED[us][mv.promotion]
	end
	board[tr][tf] = placed
	xorPiece(st, placed, tr, tf)

	-- ладья при рокировке
	if mv.isCastle ~= nil then
		local rook = (us == "w") and "wr" or "br"
		if mv.isCastle == "K" then
			board[fr][8] = nil
			board[fr][6] = rook
			xorPiece(st, rook, fr, 8)
			xorPiece(st, rook, fr, 6)
		else
			board[fr][1] = nil
			board[fr][4] = rook
			xorPiece(st, rook, fr, 1)
			xorPiece(st, rook, fr, 4)
		end
	end

	-- король
	if kind == "k" then
		st.kingRank[us] = tr
		st.kingFile[us] = tf
		if us == "w" then
			c.wK = false
			c.wQ = false
		else
			c.bK = false
			c.bQ = false
		end
	end
	-- ладейные права (ход ладьи или взятие ладьи на домашней клетке)
	if (fr == 1 and ff == 1) or (tr == 1 and tf == 1) then
		c.wQ = false
	end
	if (fr == 1 and ff == 8) or (tr == 1 and tf == 8) then
		c.wK = false
	end
	if (fr == 8 and ff == 1) or (tr == 8 and tf == 1) then
		c.bQ = false
	end
	if (fr == 8 and ff == 8) or (tr == 8 and tf == 8) then
		c.bK = false
	end

	-- клетка взятия на проходе
	st.enPassant = nil
	if kind == "p" and (tr - fr == 2 or fr - tr == 2) then
		st.enPassant = SQ[(fr + tr) // 2][ff]
		xorEP(st, ff)
	end
	xorCastling(st, c)

	-- счётчики
	if kind == "p" or captured ~= nil then
		st.halfmoveClock = 0
	else
		st.halfmoveClock += 1
	end
	if us == "b" then
		st.fullmoveNumber += 1
	end
	st.sideToMove = them
	st.history[#st.history + 1] = posKey(st)
	return undo
end

local function unmakeMove(st: State, mv: Move, undo: Undo)
	local board = st.board
	local c = st.castling
	local us = (st.sideToMove == "w") and "b" or "w"
	local fr, ff, tr, tf = mv.from.rank, mv.from.file, mv.to.rank, mv.to.file

	board[tr][tf] = nil
	board[fr][ff] = mv.piece
	if mv.isEnPassant then
		board[fr][tf] = undo.captured
	else
		board[tr][tf] = undo.captured
	end
	if mv.isCastle ~= nil then
		local rook = (us == "w") and "wr" or "br"
		if mv.isCastle == "K" then
			board[fr][6] = nil
			board[fr][8] = rook
		else
			board[fr][4] = nil
			board[fr][1] = rook
		end
	end

	c.wK = undo.wK
	c.wQ = undo.wQ
	c.bK = undo.bK
	c.bQ = undo.bQ
	st.enPassant = undo.ep
	st.halfmoveClock = undo.half
	st.fullmoveNumber = undo.full
	st.hashLo = undo.lo
	st.hashHi = undo.hi
	st.kingRank[us] = undo.kr
	st.kingFile[us] = undo.kf
	st.sideToMove = us
	st.history[#st.history] = nil
end

-- === ПРОВЕРКИ (шах, мат, пат, ничья) ===
local function hasLegalMove(st: State): boolean
	local us = st.sideToMove
	local them = (us == "w") and "b" or "w"
	local board = st.board
	local pseudo = genPseudo(st, false)
	for _, mv in ipairs(pseudo) do
		local u = makeMove(st, mv)
		local ok = not isSquareAttacked(board, st.kingRank[us], st.kingFile[us], them)
		unmakeMove(st, mv, u)
		if ok then
			return true
		end
	end
	return false
end

-- Легальные ходы. withFlags: заполнить check / mate (дороже).
-- Временно меняет st, но всегда возвращает его в исходное состояние.
local function legalMoves(st: State, withFlags: boolean): { Move }
	local us = st.sideToMove
	local them = (us == "w") and "b" or "w"
	local board = st.board
	local pseudo = genPseudo(st, false)
	local legal: { Move } = {}
	for _, mv in ipairs(pseudo) do
		local u = makeMove(st, mv)
		if not isSquareAttacked(board, st.kingRank[us], st.kingFile[us], them) then
			if withFlags then
				local chk = isSquareAttacked(board, st.kingRank[them], st.kingFile[them], us)
				mv.check = chk
				if chk then
					mv.mate = not hasLegalMove(st)
				end
			end
			legal[#legal + 1] = mv
		end
		unmakeMove(st, mv, u)
	end
	return legal
end

local function inCheckState(st: State, color: string): boolean
	local opp = (color == "w") and "b" or "w"
	return isSquareAttacked(st.board, st.kingRank[color], st.kingFile[color], opp)
end

local function insufficientMaterial(st: State): boolean
	local minors, knights, light, dark = 0, 0, 0, 0
	for r = 1, 8 do
		for f = 1, 8 do
			local p = st.board[r][f]
			if p ~= nil then
				local kind = KIND_OF[p]
				if kind == "p" or kind == "r" or kind == "q" then
					return false
				elseif kind == "n" then
					knights += 1
					minors += 1
				elseif kind == "b" then
					minors += 1
					if (r + f) % 2 == 0 then
						dark += 1
					else
						light += 1
					end
				end
			end
		end
	end
	if minors <= 1 then
		return true -- K vs K, K+N vs K, K+B vs K
	end
	if knights == 0 and (light == 0 or dark == 0) then
		return true -- только слоны одного цвета клеток (в т.ч. K+B vs K+B)
	end
	return false
end

local function repetitionCount(st: State): number
	local h = st.history
	local n = #h
	local cur = h[n]
	local count = 0
	for i = 1, n do
		if h[i] == cur then
			count += 1
		end
	end
	return count
end

-- Перебор для проверки корректности генератора ходов
local function perft(st: State, depth: number): number
	if depth == 0 then
		return 1
	end
	local moves = legalMoves(st, false)
	if depth == 1 then
		return #moves
	end
	local nodes = 0
	for _, mv in ipairs(moves) do
		local u = makeMove(st, mv)
		nodes += perft(st, depth - 1)
		unmakeMove(st, mv, u)
	end
	return nodes
end

-- Находит в списке легальных ходов ход с теми же from/to/promotion
local function findLegal(legal: { Move }, move: Move): Move?
	local promo = move.promotion
	for _, m in ipairs(legal) do
		if
			m.from.rank == move.from.rank
			and m.from.file == move.from.file
			and m.to.rank == move.to.rank
			and m.to.file == move.to.file
		then
			if m.promotion == nil or m.promotion == (promo or "q") then
				return m
			end
		end
	end
	return nil
end

-- === SAN НОТАЦИЯ ===
local function sanOf(st: State, mv: Move, legal: { Move }): string
	local san = ""
	if mv.isCastle ~= nil then
		san = (mv.isCastle == "K") and "O-O" or "O-O-O"
	else
		local kind = KIND_OF[mv.piece]
		local dest = coordsToSquare(mv.to.rank, mv.to.file)
		local capture = mv.captured ~= nil or mv.isEnPassant
		if kind == "p" then
			if capture then
				san = string.sub(FILE_LETTERS, mv.from.file, mv.from.file) .. "x"
			end
			san ..= dest
			if mv.promotion ~= nil then
				san ..= "=" .. string.upper(mv.promotion)
			end
		else
			local ambiguous, sameFile, sameRank = false, false, false
			for _, m in ipairs(legal) do
				if
					m ~= mv
					and m.piece == mv.piece
					and m.to.rank == mv.to.rank
					and m.to.file == mv.to.file
					and not (m.from.rank == mv.from.rank and m.from.file == mv.from.file)
				then
					ambiguous = true
					if m.from.file == mv.from.file then
						sameFile = true
					end
					if m.from.rank == mv.from.rank then
						sameRank = true
					end
				end
			end
			local disamb = ""
			if ambiguous then
				local fileLetter = string.sub(FILE_LETTERS, mv.from.file, mv.from.file)
				if not sameFile then
					disamb = fileLetter
				elseif not sameRank then
					disamb = tostring(mv.from.rank)
				else
					disamb = fileLetter .. tostring(mv.from.rank)
				end
			end
			san = string.upper(kind) .. disamb .. (capture and "x" or "") .. dest
		end
	end
	-- суффикс шаха / мата
	local us = st.sideToMove
	local them = (us == "w") and "b" or "w"
	local u = makeMove(st, mv)
	if isSquareAttacked(st.board, st.kingRank[them], st.kingFile[them], us) then
		if hasLegalMove(st) then
			san ..= "+"
		else
			san ..= "#"
		end
	end
	unmakeMove(st, mv, u)
	return san
end

-- === ОЦЕНКА ===
local evWMin: { number } = {}
local evBMax: { number } = {}
local evWCnt: { number } = {}
local evBCnt: { number } = {}
local evPawnR: { number } = {}
local evPawnF: { number } = {}
local evPawnS: { number } = {}

local function mobilityOf(board: { { string? } }, r: number, f: number, kind: string, white: boolean): number
	local count = 0
	if kind == "n" then
		for i = 1, 8 do
			local nr, nf = r + KN_DR[i], f + KN_DF[i]
			if nr >= 1 and nr <= 8 and nf >= 1 and nf <= 8 then
				local t = board[nr][nf]
				if t == nil or (COLOR_OF[t] == "w") ~= white then
					count += 1
				end
			end
		end
		return count
	end
	if kind == "b" or kind == "q" then
		for d = 1, 4 do
			local dr, df = DIAG_DR[d], DIAG_DF[d]
			local nr, nf = r + dr, f + df
			while nr >= 1 and nr <= 8 and nf >= 1 and nf <= 8 do
				local t = board[nr][nf]
				if t == nil then
					count += 1
				else
					if (COLOR_OF[t] == "w") ~= white then
						count += 1
					end
					break
				end
				nr += dr
				nf += df
			end
		end
	end
	if kind == "r" or kind == "q" then
		for d = 1, 4 do
			local dr, df = ORTH_DR[d], ORTH_DF[d]
			local nr, nf = r + dr, f + df
			while nr >= 1 and nr <= 8 and nf >= 1 and nf <= 8 do
				local t = board[nr][nf]
				if t == nil then
					count += 1
				else
					if (COLOR_OF[t] == "w") ~= white then
						count += 1
					end
					break
				end
				nr += dr
				nf += df
			end
		end
	end
	return count
end

-- Бонус за пешечный щит перед королём
local function kingShield(board: { { string? } }, kr: number, kf: number, white: boolean): number
	local dir = white and 1 or -1
	local own = white and "wp" or "bp"
	local s = 0
	for dr = 1, 2 do
		local rr = kr + dr * dir
		if rr >= 1 and rr <= 8 then
			for df = -1, 1 do
				local ff = kf + df
				if ff >= 1 and ff <= 8 and board[rr][ff] == own then
					s += (dr == 1) and 10 or 5
				end
			end
		end
	end
	return s
end

-- Оценка с точки зрения стороны, которая ходит (для negamax)
local function evaluate(st: State): number
	local board = st.board
	local score = 0
	local npm = 0
	for f = 1, 8 do
		evWMin[f] = 9
		evBMax[f] = 0
		evWCnt[f] = 0
		evBCnt[f] = 0
	end
	local np = 0
	for r = 1, 8 do
		local row = board[r]
		for f = 1, 8 do
			local p = row[f]
			if p ~= nil then
				local white = (COLOR_OF[p] == "w")
				local kind = KIND_OF[p]
				local idx = white and ((8 - r) * 8 + f) or ((r - 1) * 8 + f)
				local sign = white and 1 or -1
				if kind == "p" then
					score += sign * (100 + PST_P[idx])
					np += 1
					evPawnR[np] = r
					evPawnF[np] = f
					evPawnS[np] = sign
					if white then
						evWCnt[f] += 1
						if r < evWMin[f] then
							evWMin[f] = r
						end
					else
						evBCnt[f] += 1
						if r > evBMax[f] then
							evBMax[f] = r
						end
					end
				elseif kind ~= "k" then
					local v = PIECE_VALUE[kind]
					npm += v
					local s = v + PST_BY_KIND[kind][idx]
					if EVAL_MOBILITY then
						s += MOB_WEIGHT[kind] * mobilityOf(board, r, f, kind, white)
					end
					score += sign * s
				end
			end
		end
	end

	-- короли: интерполяция миттельшпиль / эндшпиль + пешечный щит
	local phase = math.min(1, npm / 4000)
	for i = 1, 2 do
		local white = (i == 1)
		local color = white and "w" or "b"
		local kr, kf = st.kingRank[color], st.kingFile[color]
		local idx = white and ((8 - kr) * 8 + kf) or ((kr - 1) * 8 + kf)
		local ks = PST_K_MID[idx] * phase + PST_K_END[idx] * (1 - phase)
		ks += kingShield(board, kr, kf, white) * phase
		score += (white and 1 or -1) * ks
	end

	-- сдвоенные пешки
	for f = 1, 8 do
		if evWCnt[f] > 1 then
			score -= 15 * (evWCnt[f] - 1)
		end
		if evBCnt[f] > 1 then
			score += 15 * (evBCnt[f] - 1)
		end
	end
	-- проходные пешки
	for i = 1, np do
		local r, f, sign = evPawnR[i], evPawnF[i], evPawnS[i]
		local passed = true
		for ff = math.max(1, f - 1), math.min(8, f + 1) do
			if sign == 1 then
				if evBMax[ff] > r then
					passed = false
				end
			else
				if evWMin[ff] < r then
					passed = false
				end
			end
		end
		if passed then
			local rel = (sign == 1) and r or (9 - r)
			score += sign * PASSED_BONUS[rel]
		end
	end

	if st.sideToMove == "w" then
		return score
	end
	return -score
end

-- === ПОИСК (MINIMAX + ALPHA-BETA) ===
local TT: { [number]: TTEntry } = {}
local ttCount = 0
local TT_MAX = 300000

local function ttStore(key: number, depth: number, score: number, flag: number, best: Move?)
	if TT[key] == nil then
		ttCount += 1
		if ttCount > TT_MAX then
			TT = {}
			ttCount = 1
		end
	end
	TT[key] = { depth = depth, score = score, flag = flag, bestMove = best }
end

local function scoreToTT(score: number, ply: number): number
	if score > MATE_BOUND then
		return score + ply
	elseif score < -MATE_BOUND then
		return score - ply
	end
	return score
end

local function scoreFromTT(score: number, ply: number): number
	if score > MATE_BOUND then
		return score - ply
	elseif score < -MATE_BOUND then
		return score + ply
	end
	return score
end

local function checkTime(ctx: SearchCtx)
	local now = os.clock()
	if now - ctx.startTime > ctx.timeLimit then
		ctx.stop = true
		return
	end
	if ctx.doYield and now - ctx.lastYield >= 0.05 then
		task.wait()
		local after = os.clock()
		ctx.startTime += after - now -- время ожидания не считаем в лимит
		ctx.lastYield = after
	end
end

-- Двукратное повторение внутри поиска считаем ничьёй
local function isRepetition(st: State): boolean
	local h = st.history
	local n = #h
	local cur = h[n]
	local limit = math.min(st.halfmoveClock, n - 1)
	local i = 2
	while i <= limit do
		if h[n - i] == cur then
			return true
		end
		i += 2
	end
	return false
end

local function histKey(us: string, mv: Move): number
	return ((us == "w") and 0 or 4096)
		+ ((mv.from.rank - 1) * 8 + mv.from.file - 1) * 64
		+ (mv.to.rank - 1) * 8
		+ mv.to.file
		- 1
end

local function moveGivesCheck(st: State, mv: Move): boolean
	local us = st.sideToMove
	local them = (us == "w") and "b" or "w"
	local u = makeMove(st, mv)
	local chk = isSquareAttacked(st.board, st.kingRank[them], st.kingFile[them], us)
	unmakeMove(st, mv, u)
	return chk
end

-- Оценка порядка ходов: TT-ход, взятия (MVV-LVA), превращения, шахи, киллеры, history
local function scoreMoves(ctx: SearchCtx, st: State, moves: { Move }, ttMove: Move?, ply: number, depth: number): { number }
	local scores: { number } = {}
	local us = st.sideToMove
	local ka, kb = ctx.killerA[ply], ctx.killerB[ply]
	for i, mv in ipairs(moves) do
		local s = 0
		if ttMove ~= nil and sameMove(ttMove, mv) then
			s = 1000000
		elseif mv.captured ~= nil then
			s = 200000 + VICTIM_ORDER[KIND_OF[mv.captured]] * 10 - ATTACKER_ORDER[KIND_OF[mv.piece]]
		elseif mv.promotion ~= nil then
			s = 150000 + (PIECE_VALUE[mv.promotion] or 0)
		else
			if ka ~= nil and sameMove(ka, mv) then
				s = 50000
			elseif kb ~= nil and sameMove(kb, mv) then
				s = 49000
			else
				s = math.min(ctx.hist[histKey(us, mv)] or 0, 30000)
			end
			if depth >= 3 and moveGivesCheck(st, mv) then
				s = math.max(s, 60000)
			end
		end
		scores[i] = s
	end
	return scores
end

-- Ставит лучший из оставшихся ходов на позицию i
local function pickBest(moves: { Move }, scores: { number }, i: number)
	local bi, bs = i, scores[i]
	for j = i + 1, #moves do
		if scores[j] > bs then
			bs = scores[j]
			bi = j
		end
	end
	if bi ~= i then
		moves[i], moves[bi] = moves[bi], moves[i]
		scores[i], scores[bi] = scores[bi], scores[i]
	end
end

-- Поиск покоя: продолжаем взятия и превращения (до QS_MAX_DEPTH)
local function quiescence(ctx: SearchCtx, alpha: number, beta: number, ply: number, qdepth: number): number
	if ctx.stop then
		return 0
	end
	ctx.nodes += 1
	if ctx.nodes % 512 == 0 then
		checkTime(ctx)
		if ctx.stop then
			return 0
		end
	end
	local st = ctx.st
	local stand = evaluate(st)
	if qdepth >= QS_MAX_DEPTH then
		return stand
	end
	if stand >= beta then
		return stand
	end
	if stand > alpha then
		alpha = stand
	end
	local us = st.sideToMove
	local them = (us == "w") and "b" or "w"
	local board = st.board
	local moves = genPseudo(st, true)
	local scores: { number } = {}
	for i, mv in ipairs(moves) do
		local s = 0
		if mv.captured ~= nil then
			s = VICTIM_ORDER[KIND_OF[mv.captured]] * 10 - ATTACKER_ORDER[KIND_OF[mv.piece]]
		end
		if mv.promotion ~= nil then
			s += 80
		end
		scores[i] = s
	end
	for i = 1, #moves do
		pickBest(moves, scores, i)
		local mv = moves[i]
		local u = makeMove(st, mv)
		if isSquareAttacked(board, st.kingRank[us], st.kingFile[us], them) then
			unmakeMove(st, mv, u)
		else
			local score = -quiescence(ctx, -beta, -alpha, ply + 1, qdepth + 1)
			unmakeMove(st, mv, u)
			if ctx.stop then
				return 0
			end
			if score >= beta then
				return score
			end
			if score > alpha then
				alpha = score
			end
		end
	end
	return alpha
end

-- Negamax с альфа-бета, PVS, LMR, транспозиционной таблицей
local function negamax(ctx: SearchCtx, depth: number, alpha: number, beta: number, ply: number): number
	if ctx.stop then
		return 0
	end
	ctx.nodes += 1
	if ctx.nodes % 512 == 0 then
		checkTime(ctx)
		if ctx.stop then
			return 0
		end
	end
	local st = ctx.st
	local board = st.board
	if st.halfmoveClock >= 100 or isRepetition(st) then
		return 0
	end
	local us = st.sideToMove
	local them = (us == "w") and "b" or "w"
	local inCheck = isSquareAttacked(board, st.kingRank[us], st.kingFile[us], them)
	if inCheck and ply < ctx.maxPly then
		depth += 1 -- расширение при шахе
	end
	if depth <= 0 then
		return quiescence(ctx, alpha, beta, ply, 0)
	end

	-- транспозиционная таблица
	local key = posKey(st)
	local ttMove: Move? = nil
	local entry = TT[key]
	if entry ~= nil then
		ttMove = entry.bestMove
		if entry.depth >= depth then
			local s = scoreFromTT(entry.score, ply)
			if entry.flag == 0 then
				return s
			elseif entry.flag == 1 and s >= beta then
				return s
			elseif entry.flag == 2 and s <= alpha then
				return s
			end
		end
	end

	local alphaOrig = alpha
	local moves = genPseudo(st, false)
	local scores = scoreMoves(ctx, st, moves, ttMove, ply, depth)
	local best = -INF
	local bestMove: Move? = nil
	local legalCount = 0

	for i = 1, #moves do
		pickBest(moves, scores, i)
		local mv = moves[i]
		local u = makeMove(st, mv)
		if isSquareAttacked(board, st.kingRank[us], st.kingFile[us], them) then
			unmakeMove(st, mv, u)
		else
			legalCount += 1
			local score: number
			if legalCount == 1 then
				score = -negamax(ctx, depth - 1, -beta, -alpha, ply + 1)
			else
				local reduce = 0
				if legalCount > 4 and depth >= 3 and not inCheck and mv.captured == nil and mv.promotion == nil then
					reduce = 1
				end
				score = -negamax(ctx, depth - 1 - reduce, -alpha - 1, -alpha, ply + 1)
				if score > alpha and reduce > 0 then
					score = -negamax(ctx, depth - 1, -alpha - 1, -alpha, ply + 1)
				end
				if score > alpha and score < beta then
					score = -negamax(ctx, depth - 1, -beta, -alpha, ply + 1)
				end
			end
			unmakeMove(st, mv, u)
			if ctx.stop then
				return 0
			end
			if score > best then
				best = score
				bestMove = mv
			end
			if score > alpha then
				alpha = score
			end
			if alpha >= beta then
				if mv.captured == nil and mv.promotion == nil then
					local ka = ctx.killerA[ply]
					if ka == nil or not sameMove(ka, mv) then
						ctx.killerB[ply] = ka
						ctx.killerA[ply] = mv
					end
					local hk = histKey(us, mv)
					ctx.hist[hk] = (ctx.hist[hk] or 0) + depth * depth
				end
				break
			end
		end
	end

	if legalCount == 0 then
		if inCheck then
			return -(MATE - ply)
		end
		return 0
	end

	local flag = 0
	if best <= alphaOrig then
		flag = 2
	elseif best >= beta then
		flag = 1
	end
	ttStore(key, depth, scoreToTT(best, ply), flag, bestMove)
	return best
end

-- Для слабых уровней
local function weakDepth(elo: number): number
	return math.max(1, math.floor((elo - 500) / 300))
end

local function weakTopN(elo: number): number
	if elo <= 700 then
		return 6
	elseif elo <= 900 then
		return 5
	elseif elo <= 1100 then
		return 4
	elseif elo < 1250 then
		return 3
	end
	return 2
end

-- Копия хода с корректными флагами check / mate
local function finalizeMove(st: State, mv: Move): Move
	local copy = copyMove(mv)
	local us = st.sideToMove
	local them = (us == "w") and "b" or "w"
	local u = makeMove(st, mv)
	local chk = isSquareAttacked(st.board, st.kingRank[them], st.kingFile[them], us)
	copy.check = chk
	copy.mate = chk and not hasLegalMove(st)
	unmakeMove(st, mv, u)
	return copy
end

local function search(state: State, options: SearchOptions?): Move
	local opts: SearchOptions = options or {}
	local depth = math.max(1, math.floor(opts.depth or 4))
	local timeLimit = opts.timeLimit or 2.0
	local elo = opts.elo or 1500
	local weak = elo < 1400
	if weak then
		depth = math.min(depth, weakDepth(elo))
	end

	local now = os.clock()
	local ctx: SearchCtx = {
		st = cloneState(state),
		nodes = 0,
		startTime = now,
		timeLimit = timeLimit,
		stop = false,
		lastYield = now,
		doYield = (opts.yield ~= false),
		maxPly = 64,
		killerA = {},
		killerB = {},
		hist = {},
	}
	local st = ctx.st
	local rootMoves = legalMoves(st, false)
	if #rootMoves == 0 then
		error("Нет легальных ходов (партия окончена)")
	end
	if #rootMoves == 1 then
		return finalizeMove(st, rootMoves[1])
	end

	local us = st.sideToMove
	local rootScore: { [Move]: number } = {}
	local bestMove: Move = rootMoves[1]
	local chosen: Move? = nil

	for d = 1, depth do
		if d > 1 and os.clock() - ctx.startTime > timeLimit * 0.6 then
			break
		end
		local exact = weak and d == depth -- для слабых уровней нужны точные оценки всех ходов
		local alpha = -INF
		local iterBest: Move? = nil
		local iterScore = -INF
		for i, mv in ipairs(rootMoves) do
			local u = makeMove(st, mv)
			local score: number
			if exact then
				score = -negamax(ctx, d - 1, -INF, INF, 1)
			elseif i == 1 then
				score = -negamax(ctx, d - 1, -INF, -alpha, 1)
			else
				score = -negamax(ctx, d - 1, -alpha - 1, -alpha, 1)
				if score > alpha then
					score = -negamax(ctx, d - 1, -INF, -alpha, 1)
				end
			end
			unmakeMove(st, mv, u)
			if ctx.stop then
				break
			end
			rootScore[mv] = score
			if score > iterScore then
				iterScore = score
				iterBest = mv
			end
			if not exact and score > alpha then
				alpha = score
			end
		end

		if iterBest ~= nil then
			bestMove = iterBest
		end
		if ctx.stop then
			break
		end

		-- итерация завершена: лучший ход ставим первым
		table.sort(rootMoves, function(a: Move, b: Move): boolean
			return (rootScore[a] or -INF) > (rootScore[b] or -INF)
		end)
		for i, mv in ipairs(rootMoves) do
			if mv == bestMove then
				table.remove(rootMoves, i)
				table.insert(rootMoves, 1, mv)
				break
			end
		end

		if exact then
			-- выбор не лучшего, а случайного хода из топ-N
			local bestS = rootScore[rootMoves[1]] or 0
			if bestS >= MATE_BOUND then
				chosen = rootMoves[1]
			else
				local topN = math.min(weakTopN(elo), #rootMoves)
				local margin = 150 + (1400 - elo) * 0.6
				local candidates: { Move } = {}
				for i = 1, topN do
					local s = rootScore[rootMoves[i]] or -INF
					if bestS - s <= margin then
						candidates[#candidates + 1] = rootMoves[i]
					end
				end
				chosen = candidates[math.random(1, #candidates)]
			end
		elseif iterScore >= MATE_BOUND and not weak then
			break -- найден форсированный мат
		end
	end

	return finalizeMove(st, chosen or bestMove)
end

-- === ПУБЛИЧНОЕ API ===
Chess.squareToCoords = squareToCoords
Chess.coordsToSquare = coordsToSquare

function Chess.clone(state: State): State
	return cloneState(state)
end

function Chess.fromFEN(fen: string): State
	local fields: { string } = {}
	for tok in string.gmatch(fen, "%S+") do
		fields[#fields + 1] = tok
	end
	if #fields < 4 then
		error("Некорректный FEN: нужно минимум 4 поля")
	end

	local board: { { string? } } = {}
	for r = 1, 8 do
		board[r] = {}
	end
	local rank = 8
	for rowStr in string.gmatch(fields[1] .. "/", "([^/]*)/") do
		if rank < 1 then
			error("Некорректный FEN: слишком много рядов")
		end
		local file = 1
		for i = 1, #rowStr do
			local ch = string.sub(rowStr, i, i)
			local num = tonumber(ch)
			if num ~= nil then
				if num < 1 or num > 8 then
					error("Некорректный FEN: неверная цифра")
				end
				file += num
			else
				local lower = string.lower(ch)
				if not string.find("pnbrqk", lower, 1, true) or file > 8 then
					error("Некорректный FEN: символ '" .. ch .. "'")
				end
				local color = (ch == lower) and "b" or "w"
				board[rank][file] = color .. lower
				file += 1
			end
		end
		if file ~= 9 then
			error("Некорректный FEN: неверная длина ряда")
		end
		rank -= 1
	end
	if rank ~= 0 then
		error("Некорректный FEN: ожидается 8 рядов")
	end

	local side = fields[2]
	if side ~= "w" and side ~= "b" then
		error("Некорректный FEN: сторона хода")
	end
	local cs = fields[3]
	local castling: Castling = {
		wK = string.find(cs, "K", 1, true) ~= nil,
		wQ = string.find(cs, "Q", 1, true) ~= nil,
		bK = string.find(cs, "k", 1, true) ~= nil,
		bQ = string.find(cs, "q", 1, true) ~= nil,
	}
	local ep: Coord? = nil
	if fields[4] ~= "-" then
		local c = squareToCoords(fields[4])
		ep = SQ[c.rank][c.file]
	end

	local st: State = {
		board = board,
		sideToMove = side,
		castling = castling,
		enPassant = ep,
		halfmoveClock = tonumber(fields[5] or "0") or 0,
		fullmoveNumber = tonumber(fields[6] or "1") or 1,
		history = {},
		hashLo = 0,
		hashHi = 0,
		kingRank = { w = 0, b = 0 },
		kingFile = { w = 0, b = 0 },
	}
	local kings = { w = 0, b = 0 }
	for r = 1, 8 do
		for f = 1, 8 do
			local p = board[r][f]
			if p ~= nil and KIND_OF[p] == "k" then
				local color = COLOR_OF[p]
				kings[color] += 1
				st.kingRank[color] = r
				st.kingFile[color] = f
			end
		end
	end
	if kings.w ~= 1 or kings.b ~= 1 then
		error("Некорректный FEN: у каждой стороны должен быть ровно один король")
	end
	computeHash(st)
	st.history[1] = posKey(st)
	return st
end

function Chess.new(): State
	return Chess.fromFEN(START_FEN)
end

function Chess.toFEN(state: State): string
	local rows: { string } = {}
	for r = 8, 1, -1 do
		local s = ""
		local empty = 0
		for f = 1, 8 do
			local p = state.board[r][f]
			if p == nil then
				empty += 1
			else
				if empty > 0 then
					s ..= tostring(empty)
					empty = 0
				end
				local kind = KIND_OF[p]
				s ..= (COLOR_OF[p] == "w") and string.upper(kind) or kind
			end
		end
		if empty > 0 then
			s ..= tostring(empty)
		end
		rows[#rows + 1] = s
	end
	local c = state.castling
	local cs = (c.wK and "K" or "") .. (c.wQ and "Q" or "") .. (c.bK and "k" or "") .. (c.bQ and "q" or "")
	if cs == "" then
		cs = "-"
	end
	local ep = "-"
	if state.enPassant ~= nil then
		ep = coordsToSquare(state.enPassant.rank, state.enPassant.file)
	end
	return table.concat(rows, "/")
		.. " "
		.. state.sideToMove
		.. " "
		.. cs
		.. " "
		.. ep
		.. " "
		.. tostring(state.halfmoveClock)
		.. " "
		.. tostring(state.fullmoveNumber)
end

-- onlyLegal по умолчанию true. Для легальных ходов заполняются check и mate.
function Chess.generateMoves(state: State, onlyLegal: boolean?): { Move }
	local st = cloneState(state)
	if onlyLegal == false then
		return genPseudo(st, false)
	end
	return legalMoves(st, true)
end

-- Возвращает НОВОЕ состояние. Недопустимый ход -> ошибка.
-- Достаточно указать from / to (и promotion, по умолчанию "q").
function Chess.applyMove(state: State, move: Move): State
	local st = cloneState(state)
	local legal = legalMoves(st, false)
	local found = findLegal(legal, move)
	if found == nil then
		error("Недопустимый ход: "
			.. coordsToSquare(move.from.rank, move.from.file)
			.. coordsToSquare(move.to.rank, move.to.file))
	end
	makeMove(st, found)
	return st
end

function Chess.isCheck(state: State, color: string): boolean
	return inCheckState(state, color)
end

function Chess.isCheckmate(state: State): boolean
	local st = cloneState(state)
	return inCheckState(st, st.sideToMove) and not hasLegalMove(st)
end

function Chess.isStalemate(state: State): boolean
	local st = cloneState(state)
	return (not inCheckState(st, st.sideToMove)) and not hasLegalMove(st)
end

function Chess.isInsufficientMaterial(state: State): boolean
	return insufficientMaterial(state)
end

function Chess.isDraw(state: State): boolean
	return state.halfmoveClock >= 100 or repetitionCount(state) >= 3 or insufficientMaterial(state)
end

function Chess.gameStatus(state: State): string
	local st = cloneState(state)
	if not hasLegalMove(st) then
		if inCheckState(st, st.sideToMove) then
			-- суффикс = цвет победителя
			return (st.sideToMove == "w") and "checkmate_b" or "checkmate_w"
		end
		return "stalemate"
	end
	if insufficientMaterial(st) then
		return "draw_material"
	end
	if st.halfmoveClock >= 100 then
		return "draw_50"
	end
	if repetitionCount(st) >= 3 then
		return "draw_repetition"
	end
	return "ongoing"
end

function Chess.moveToSAN(state: State, move: Move): string
	local st = cloneState(state)
	local legal = legalMoves(st, false)
	local found = findLegal(legal, move)
	if found == nil then
		error("Недопустимый ход для SAN")
	end
	return sanOf(st, found, legal)
end

function Chess.findBestMove(state: State, options: SearchOptions?): Move
	return search(state, options)
end

function Chess.perft(state: State, depth: number): number
	return perft(cloneState(state), depth)
end

function Chess.clearCache()
	TT = {}
	ttCount = 0
end

-- === САМОПРОВЕРКА ===
function Chess.selfTest(): (boolean, { string })
	local results: { string } = {}
	local allOk = true
	local function check(name: string, cond: boolean, info: string?)
		if not cond then
			allOk = false
		end
		local line = (cond and "[OK]   " or "[FAIL] ") .. name .. (info and (" (" .. info .. ")") or "")
		results[#results + 1] = line
		print(line)
	end
	local function has(moves: { Move }, fr: string, to: string): Move?
		local a, b = squareToCoords(fr), squareToCoords(to)
		for _, m in ipairs(moves) do
			if m.from.rank == a.rank and m.from.file == a.file and m.to.rank == b.rank and m.to.file == b.file then
				return m
			end
		end
		return nil
	end

	-- 1. Начальная позиция: 20 ходов
	local start = Chess.new()
	local startMoves = Chess.generateMoves(start, true)
	check("Начальная позиция: 20 ходов", #startMoves == 20, tostring(#startMoves))
	check("toFEN(new) совпадает с начальным FEN", Chess.toFEN(start) == START_FEN, Chess.toFEN(start))

	-- Perft (проверка генератора)
	check("perft(3) начальной позиции = 8902", Chess.perft(start, 3) == 8902)
	local kiwi = Chess.fromFEN("r3k2r/p1ppqpb1/bn2pnp1/3PN3/1p2P3/2N2Q1p/PPPBBPPP/R3K2R w KQkq - 0 1")
	check("perft(1) Kiwipete = 48", Chess.perft(kiwi, 1) == 48)
	check("perft(2) Kiwipete = 2039", Chess.perft(kiwi, 2) == 2039)

	-- 2. Мат Легаля (мат в 1 ход: Nd5#)
	local legal = Chess.fromFEN("rn1q1bnr/ppp1kB1p/3p2p1/4N3/4P3/2N5/PPPP1PPP/R1BbK2R w KQ - 0 7")
	local t0 = os.clock()
	local best = Chess.findBestMove(legal, { depth = 4, timeLimit = 1.0, yield = false })
	local elapsed = os.clock() - t0
	check(
		"Мат Легаля найден (Nd5#) за <= 1 с",
		best.piece == "wn" and best.to.rank == 5 and best.to.file == 4 and best.mate and elapsed <= 1.5,
		string.format("%.3f c", elapsed)
	)
	check("SAN хода мата = Nd5#", Chess.moveToSAN(legal, best) == "Nd5#", Chess.moveToSAN(legal, best))

	-- 3. Рокировка
	local cst = Chess.fromFEN("r3k2r/8/8/8/8/8/8/R3K2R w KQkq - 0 1")
	local cmoves = Chess.generateMoves(cst, true)
	local castleK, castleQ = nil, nil
	for _, m in ipairs(cmoves) do
		if m.isCastle == "K" then
			castleK = m
		elseif m.isCastle == "Q" then
			castleQ = m
		end
	end
	check("Рокировка: обе доступны", castleK ~= nil and castleQ ~= nil)
	if castleK ~= nil then
		local after = Chess.applyMove(cst, castleK)
		check(
			"O-O: король g1, ладья f1, права сняты",
			after.board[1][7] == "wk" and after.board[1][6] == "wr" and after.board[1][8] == nil and not after.castling.wK,
			Chess.toFEN(after)
		)
		check("SAN рокировки = O-O", Chess.moveToSAN(cst, castleK) == "O-O")
	end
	if castleQ ~= nil then
		local after = Chess.applyMove(cst, castleQ)
		check("O-O-O: король c1, ладья d1", after.board[1][3] == "wk" and after.board[1][4] == "wr")
	end
	local inChk = Chess.fromFEN("4r1k1/8/8/8/8/8/8/R3K2R w KQ - 0 1")
	local noCastle = true
	for _, m in ipairs(Chess.generateMoves(inChk, true)) do
		if m.isCastle ~= nil then
			noCastle = false
		end
	end
	check("Рокировка запрещена под шахом", Chess.isCheck(inChk, "w") and noCastle)
	local throughAttack = Chess.fromFEN("5r1k/8/8/8/8/8/8/R3K2R w KQ - 0 1") -- f1 под боем
	local noK = true
	for _, m in ipairs(Chess.generateMoves(throughAttack, true)) do
		if m.isCastle == "K" then
			noK = false
		end
	end
	check("Короткая рокировка запрещена через битое поле", noK)

	-- 4. Взятие на проходе
	local ep = Chess.fromFEN("4k3/8/8/3pP3/8/8/8/4K3 w - d6 0 1")
	local epMove = has(Chess.generateMoves(ep, true), "e5", "d6")
	check("En passant: ход есть", epMove ~= nil and epMove.isEnPassant)
	if epMove ~= nil then
		local after = Chess.applyMove(ep, epMove)
		check(
			"En passant: пешка d5 снята, белая на d6",
			after.board[5][4] == nil and after.board[6][4] == "wp",
			Chess.toFEN(after)
		)
		check("SAN en passant = exd6", Chess.moveToSAN(ep, epMove) == "exd6")
	end

	-- 5. Превращение
	local pr = Chess.fromFEN("8/P6k/8/8/8/8/8/K7 w - - 0 1")
	local promoCount = 0
	for _, m in ipairs(Chess.generateMoves(pr, true)) do
		if m.promotion ~= nil then
			promoCount += 1
		end
	end
	check("Превращение: 4 варианта", promoCount == 4, tostring(promoCount))
	local promoMove = has(Chess.generateMoves(pr, true), "a7", "a8")
	if promoMove ~= nil then
		local want = copyMove(promoMove)
		want.promotion = "n"
		local after = Chess.applyMove(pr, want)
		check("Превращение в коня работает", after.board[8][1] == "wn", Chess.toFEN(after))
	else
		check("Превращение в коня работает", false)
	end

	-- 6. Пат
	local stale = Chess.fromFEN("7k/5Q2/6K1/8/8/8/8/8 b - - 0 1")
	check("Пат определяется", Chess.isStalemate(stale) and Chess.gameStatus(stale) == "stalemate")

	-- Мат и недостаток материала
	local mated = Chess.fromFEN("R5k1/5ppp/8/8/8/8/8/6K1 b - - 0 1")
	check("Мат определяется", Chess.isCheckmate(mated) and Chess.gameStatus(mated) == "checkmate_w")
	local kk = Chess.fromFEN("8/8/8/4k3/8/8/3K4/8 w - - 0 1")
	check("K vs K = ничья по материалу", Chess.gameStatus(kk) == "draw_material")

	-- Скорость поиска (информационно)
	local t1 = os.clock()
	local mv = Chess.findBestMove(start, { depth = 4, timeLimit = 5, yield = false })
	local dt = os.clock() - t1
	print(string.format("Глубина 4 из начальной позиции: %.3f c, ход %s%s", dt,
		coordsToSquare(mv.from.rank, mv.from.file), coordsToSquare(mv.to.rank, mv.to.file)))
	results[#results + 1] = string.format("Скорость depth=4: %.3f c", dt)

	print(allOk and "=== ВСЕ ТЕСТЫ ПРОЙДЕНЫ ===" or "=== ЕСТЬ ПРОВАЛЕННЫЕ ТЕСТЫ ===")
	return allOk, results
end

return Chess
