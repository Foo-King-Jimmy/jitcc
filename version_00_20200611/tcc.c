/*  TCC - Tiny C Compiler
 *  Copyright (c) 2001-2004 Fabrice Bellard
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */


#include "tcc.h"

#if ONE_SOURCE

/**  #include "libtcc.c"  **/
/**  start of libtcc.c  **/

/********************************************************/
/* global variables */


ST_DATA  FILE * jjglob_dbgfh;    // sg that may be used by tcc_error() if possible
ST_DATA  int    jjglob_retval;   // collects the retval/errorcode for jitcc()
ST_DATA  int    jjglob_newdone;  // represents the state var that shows if/how we can use tcc_error
                                 // ( actually ) whether tcc_new returned at all.
ST_DATA  jmp_buf  err_jmp_buf1;
ST_DATA  jmp_buf  err_jmp_buf2;
ST_DATA  int      jmp_var;


/* use GNU C extensions */
ST_DATA int gnu_ext = 1;

/* use TinyCC extensions */
ST_DATA int tcc_ext = 1;

/* XXX: get rid of this ASAP */
ST_DATA struct TCCState *tcc_state;

static int nb_states;

/********************************************************/

#if ONE_SOURCE

/*  TCC - Tiny C Compiler
 *  Copyright (c) 2001-2004 Fabrice Bellard
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */

/********************************************************/
/* global variables */

ST_DATA int tok_flags;
ST_DATA int parse_flags;

ST_DATA struct BufferedFile *file;
ST_DATA int ch, tok;
ST_DATA CValue tokc;
ST_DATA const int *macro_ptr;
ST_DATA CString tokcstr; /* current parsed string, if any */

/* display benchmark infos */
ST_DATA int total_lines;
ST_DATA int total_bytes;
ST_DATA int tok_ident;
ST_DATA TokenSym **table_ident;

/* ------------------------------------------------------------------------- */

static TokenSym *hash_ident[TOK_HASH_SIZE];
static char token_buf[STRING_MAX_SIZE + 1];
static CString cstr_buf;
static CString macro_equal_buf;
static TokenString tokstr_buf;
static unsigned char isidnum_table[256 - CH_EOF];
static int pp_debug_tok, pp_debug_symv;
static int pp_once;
static int pp_expr;
static int pp_counter;

static struct TinyAlloc *toksym_alloc;
static struct TinyAlloc *tokstr_alloc;
static struct TinyAlloc *cstr_alloc;

static TokenString *macro_stack;

static const char tcc_keywords[] = 
#define DEF(id, str) str "\0"
#include "tcctok.h"
#undef DEF
;

/* WARNING: the content of this string encodes token numbers */
static const unsigned char tok_two_chars[] =
/* outdated -- gr
    "<=\236>=\235!=\225&&\240||\241++\244--\242==\224<<\1>>\2+=\253"
    "-=\255*=\252/=\257%=\245&=\246^=\336|=\374->\313..\250##\266";
*/{
    '<','=', TOK_LE,
    '>','=', TOK_GE,
    '!','=', TOK_NE,
    '&','&', TOK_LAND,
    '|','|', TOK_LOR,
    '+','+', TOK_INC,
    '-','-', TOK_DEC,
    '=','=', TOK_EQ,
    '<','<', TOK_SHL,
    '>','>', TOK_SAR,
    '+','=', TOK_A_ADD,
    '-','=', TOK_A_SUB,
    '*','=', TOK_A_MUL,
    '/','=', TOK_A_DIV,
    '%','=', TOK_A_MOD,
    '&','=', TOK_A_AND,
    '^','=', TOK_A_XOR,
    '|','=', TOK_A_OR,
    '-','>', TOK_ARROW,
    '.','.', TOK_TWODOTS,
    '#','#', TOK_TWOSHARPS,
    0
};

static void next_nomacro_spc(void);

ST_FUNC void skip(int c)
{
    if( tok != c )  tcc_error(-1, "'%c' expected (got \"%s\")", c, get_tok_str(tok, &tokc));
    next();
}


/* ------------------------------------------------------------------------- */
/* Custom allocator for tiny objects */

#define USE_TAL

#ifndef USE_TAL
#define tal_free(al, p) tcc_free(p)
#define tal_realloc(al, p, size) tcc_realloc(p, size)
#define tal_new(a,b,c)
#define tal_delete(a)
#else
#if !defined(MEM_DEBUG)
#define tal_free(al, p) tal_free_impl(al, p)
#define tal_realloc(al, p, size) tal_realloc_impl(&al, p, size)
#define TAL_DEBUG_PARAMS
#else
#define TAL_DEBUG 1
//#define TAL_INFO 1 /* collect and dump allocators stats */
#define tal_free(al, p) tal_free_impl(al, p, __FILE__, __LINE__)
#define tal_realloc(al, p, size) tal_realloc_impl(&al, p, size, __FILE__, __LINE__)
#define TAL_DEBUG_PARAMS , const char *file, int line
#define TAL_DEBUG_FILE_LEN 40
#endif

#define TOKSYM_TAL_SIZE     (768 * 1024) /* allocator for tiny TokenSym in table_ident */
#define TOKSTR_TAL_SIZE     (768 * 1024) /* allocator for tiny TokenString instances */
#define CSTR_TAL_SIZE       (256 * 1024) /* allocator for tiny CString instances */
#define TOKSYM_TAL_LIMIT    256 /* prefer unique limits to distinguish allocators debug msgs */
#define TOKSTR_TAL_LIMIT    128 /* 32 * sizeof(int) */
#define CSTR_TAL_LIMIT      1024

typedef struct TinyAlloc {
    unsigned  limit;
    unsigned  size;
    uint8_t *buffer;
    uint8_t *p;
    unsigned  nb_allocs;
    struct TinyAlloc *next, *top;
#ifdef TAL_INFO
    unsigned  nb_peak;
    unsigned  nb_total;
    unsigned  nb_missed;
    uint8_t *peak_p;
#endif
} TinyAlloc;

typedef struct tal_header_t {
    unsigned  size;
#ifdef TAL_DEBUG
    int     line_num; /* negative line_num used for double free check */
    char    file_name[TAL_DEBUG_FILE_LEN + 1];
#endif
} tal_header_t;

/* ------------------------------------------------------------------------- */

static TinyAlloc *tal_new(TinyAlloc **pal, unsigned limit, unsigned size)
{
    TinyAlloc *al = tcc_mallocz(sizeof(TinyAlloc));
    al->p = al->buffer = tcc_malloc(size);
    al->limit = limit;
    al->size = size;
    if (pal) *pal = al;
    return al;
}

static void tal_delete(TinyAlloc *al)
{
    TinyAlloc *next;

tail_call:
    if (!al)
        return;
#ifdef TAL_INFO
    fprintf(stderr, "limit=%5d, size=%5g MB, nb_peak=%6d, nb_total=%8d, nb_missed=%6d, usage=%5.1f%%\n",
            al->limit, al->size / 1024.0 / 1024.0, al->nb_peak, al->nb_total, al->nb_missed,
            (al->peak_p - al->buffer) * 100.0 / al->size);
#endif
#ifdef TAL_DEBUG
    if (al->nb_allocs > 0) {
        uint8_t *p;
        fprintf(stderr, "TAL_DEBUG: memory leak %d chunk(s) (limit= %d)\n",
                al->nb_allocs, al->limit);
        p = al->buffer;
        while (p < al->p) {
            tal_header_t *header = (tal_header_t *)p;
            if (header->line_num > 0) {
                fprintf(stderr, "%s:%d: chunk of %d bytes leaked\n",
                        header->file_name, header->line_num, header->size);
            }
            p += header->size + sizeof(tal_header_t);
        }
#if MEM_DEBUG-0 == 2
        exit( -202 );  // JJX  used to be  exit(2);
#endif
    }
#endif
    next = al->next;
    tcc_free(al->buffer);
    tcc_free(al);
    al = next;
    goto tail_call;
}

static void tal_free_impl(TinyAlloc *al, void *p TAL_DEBUG_PARAMS)
{
    if (!p)
        return;
tail_call:
    if (al->buffer <= (uint8_t *)p && (uint8_t *)p < al->buffer + al->size) {
#ifdef TAL_DEBUG
        tal_header_t *header = (((tal_header_t *)p) - 1);
        if (header->line_num < 0) {
            fprintf(stderr, "%s:%d: TAL_DEBUG: double frees chunk from\n",
                    file, line);
            fprintf(stderr, "%s:%d: %d bytes\n",
                    header->file_name, (int)-header->line_num, (int)header->size);
        } else
            header->line_num = -header->line_num;
#endif
        al->nb_allocs--;
        if (!al->nb_allocs)
            al->p = al->buffer;
    } else if (al->next) {
        al = al->next;
        goto tail_call;
    }
    else
        tcc_free(p);
}

static void *tal_realloc_impl(TinyAlloc **pal, void *p, unsigned size TAL_DEBUG_PARAMS)
{
    tal_header_t *header;
    void *ret;
    int is_own;
    unsigned adj_size = (size + 3) & -4;
    TinyAlloc *al = *pal;

tail_call:
    is_own = (al->buffer <= (uint8_t *)p && (uint8_t *)p < al->buffer + al->size);
    if ((!p || is_own) && size <= al->limit) {
        if (al->p + adj_size + sizeof(tal_header_t) < al->buffer + al->size) {
            header = (tal_header_t *)al->p;
            header->size = adj_size;
#ifdef TAL_DEBUG
            { int ofs = strlen(file) - TAL_DEBUG_FILE_LEN;
            strncpy(header->file_name, file + (ofs > 0 ? ofs : 0), TAL_DEBUG_FILE_LEN);
            header->file_name[TAL_DEBUG_FILE_LEN] = 0;
            header->line_num = line; }
#endif
            ret = al->p + sizeof(tal_header_t);
            al->p += adj_size + sizeof(tal_header_t);
            if (is_own) {
                header = (((tal_header_t *)p) - 1);
                memcpy(ret, p, header->size);
#ifdef TAL_DEBUG
                header->line_num = -header->line_num;
#endif
            } else {
                al->nb_allocs++;
            }
#ifdef TAL_INFO
            if (al->nb_peak < al->nb_allocs)
                al->nb_peak = al->nb_allocs;
            if (al->peak_p < al->p)
                al->peak_p = al->p;
            al->nb_total++;
#endif
            return ret;
        } else if (is_own) {
            al->nb_allocs--;
            ret = tal_realloc(*pal, 0, size);
            header = (((tal_header_t *)p) - 1);
            memcpy(ret, p, header->size);
#ifdef TAL_DEBUG
            header->line_num = -header->line_num;
#endif
            return ret;
        }
        if (al->next) {
            al = al->next;
        } else {
            TinyAlloc *bottom = al, *next = al->top ? al->top : al;

            al = tal_new(pal, next->limit, next->size * 2);
            al->next = next;
            bottom->top = al;
        }
        goto tail_call;
    }
    if (is_own) {
        al->nb_allocs--;
        ret = tcc_malloc(size);
        header = (((tal_header_t *)p) - 1);
        memcpy(ret, p, header->size);
#ifdef TAL_DEBUG
        header->line_num = -header->line_num;
#endif
    } else if (al->next) {
        al = al->next;
        goto tail_call;
    } else
        ret = tcc_realloc(p, size);
#ifdef TAL_INFO
    al->nb_missed++;
#endif
    return ret;
}

#endif /* USE_TAL */

/* ------------------------------------------------------------------------- */
/* CString handling */
static void cstr_realloc(CString *cstr, int new_size)
{
    int size;

    size = cstr->size_allocated;
    if (size < 8)
        size = 8; /* no need to allocate a too small first string */
    while (size < new_size)
        size = size * 2;
    cstr->data = tal_realloc(cstr_alloc, cstr->data, size);
    cstr->size_allocated = size;
}

/* add a byte */
ST_INLN void cstr_ccat(CString *cstr, int ch)
{
    int size;
    size = cstr->size + 1;
    if (size > cstr->size_allocated)
        cstr_realloc(cstr, size);
    ((unsigned char *)cstr->data)[size - 1] = ch;
    cstr->size = size;
}

ST_FUNC void cstr_cat(CString *cstr, const char *str, int len)
{
    int size;
    if (len <= 0)
        len = strlen(str) + 1 + len;
    size = cstr->size + len;
    if (size > cstr->size_allocated)
        cstr_realloc(cstr, size);
    memmove(((unsigned char *)cstr->data) + cstr->size, str, len);
    cstr->size = size;
}

/* add a wide char */
ST_FUNC void cstr_wccat(CString *cstr, int ch)
{
    int size;
    size = cstr->size + sizeof(nwchar_t);
    if (size > cstr->size_allocated)
        cstr_realloc(cstr, size);
    *(nwchar_t *)(((unsigned char *)cstr->data) + size - sizeof(nwchar_t)) = ch;
    cstr->size = size;
}

ST_FUNC void cstr_new(CString *cstr)
{
    memset(cstr, 0, sizeof(CString));
}

/* free string and reset it to NULL */
ST_FUNC void cstr_free(CString *cstr)
{
    tal_free(cstr_alloc, cstr->data);
    cstr_new(cstr);
}

/* reset string to empty */
ST_FUNC void cstr_reset(CString *cstr)
{
    cstr->size = 0;
}

/* XXX: unicode ? */
static void add_char(CString *cstr, int c)
{
    if (c == '\'' || c == '\"' || c == '\\') {
        /* XXX: could be more precise if char or string */
        cstr_ccat(cstr, '\\');
    }
    if (c >= 32 && c <= 126) {
        cstr_ccat(cstr, c);
    } else {
        cstr_ccat(cstr, '\\');
        if (c == '\n') {
            cstr_ccat(cstr, 'n');
        } else {
            cstr_ccat(cstr, '0' + ((c >> 6) & 7));
            cstr_ccat(cstr, '0' + ((c >> 3) & 7));
            cstr_ccat(cstr, '0' + (c & 7));
        }
    }
}

/* ------------------------------------------------------------------------- */
/* allocate a new token */
static TokenSym *tok_alloc_new(TokenSym **pts, const char *str, int len)
{
    TokenSym *ts, **ptable;
    int i;

    if (tok_ident >= SYM_FIRST_ANOM) 
        tcc_error(-1, "memory full (symbols)");

    /* expand token table if needed */
    i = tok_ident - TOK_IDENT;
    if ((i % TOK_ALLOC_INCR) == 0) {
        ptable = tcc_realloc(table_ident, (i + TOK_ALLOC_INCR) * sizeof(TokenSym *));
        table_ident = ptable;
    }

    ts = tal_realloc(toksym_alloc, 0, sizeof(TokenSym) + len);
    table_ident[i] = ts;
    ts->tok = tok_ident++;
    ts->sym_define = NULL;
    ts->sym_label = NULL;
    ts->sym_struct = NULL;
    ts->sym_identifier = NULL;
    ts->len = len;
    ts->hash_next = NULL;
    memcpy(ts->str, str, len);
    ts->str[len] = '\0';
    *pts = ts;
    return ts;
}

#define TOK_HASH_INIT 1
#define TOK_HASH_FUNC(h, c) ((h) + ((h) << 5) + ((h) >> 27) + (c))


/* find a token and add it if not found */
ST_FUNC TokenSym *tok_alloc(const char *str, int len)
{
    TokenSym *ts, **pts;
    int i;
    unsigned int h;
    
    h = TOK_HASH_INIT;
    for(i=0;i<len;i++)
        h = TOK_HASH_FUNC(h, ((unsigned char *)str)[i]);
    h &= (TOK_HASH_SIZE - 1);

    pts = &hash_ident[h];
    for(;;) {
        ts = *pts;
        if (!ts)
            break;
        if (ts->len == len && !memcmp(ts->str, str, len))
            return ts;
        pts = &(ts->hash_next);
    }
    return tok_alloc_new(pts, str, len);
}

/* XXX: buffer overflow */
/* XXX: float tokens */
ST_FUNC const char *get_tok_str(int v, CValue *cv)
{
    char *p;
    int i, len;

    cstr_reset(&cstr_buf);
    p = cstr_buf.data;

    switch(v) {
    case TOK_CINT:
    case TOK_CUINT:
    case TOK_CLONG:
    case TOK_CULONG:
    case TOK_CLLONG:
    case TOK_CULLONG:
        /* XXX: not quite exact, but only useful for testing  */
#ifdef _WIN32
        sprintf(p, "%u", (unsigned)cv->i);
#else
        sprintf(p, "%llu", (unsigned long long)cv->i);
#endif
        break;
    case TOK_LCHAR:
        cstr_ccat(&cstr_buf, 'L');
    case TOK_CCHAR:
        cstr_ccat(&cstr_buf, '\'');
        add_char(&cstr_buf, cv->i);
        cstr_ccat(&cstr_buf, '\'');
        cstr_ccat(&cstr_buf, '\0');
        break;
    case TOK_PPNUM:
    case TOK_PPSTR:
        return (char*)cv->str.data;
    case TOK_LSTR:
        cstr_ccat(&cstr_buf, 'L');
    case TOK_STR:
        cstr_ccat(&cstr_buf, '\"');
        if (v == TOK_STR) {
            len = cv->str.size - 1;
            for(i=0;i<len;i++)
                add_char(&cstr_buf, ((unsigned char *)cv->str.data)[i]);
        } else {
            len = (cv->str.size / sizeof(nwchar_t)) - 1;
            for(i=0;i<len;i++)
                add_char(&cstr_buf, ((nwchar_t *)cv->str.data)[i]);
        }
        cstr_ccat(&cstr_buf, '\"');
        cstr_ccat(&cstr_buf, '\0');
        break;

    case TOK_CFLOAT:
        cstr_cat(&cstr_buf, "<float>", 0);
        break;
    case TOK_CDOUBLE:
	cstr_cat(&cstr_buf, "<double>", 0);
	break;
    case TOK_CLDOUBLE:
	cstr_cat(&cstr_buf, "<long double>", 0);
	break;
    case TOK_LINENUM:
	cstr_cat(&cstr_buf, "<linenumber>", 0);
	break;

    /* above tokens have value, the ones below don't */
    case TOK_LT:
        v = '<';
        goto addv;
    case TOK_GT:
        v = '>';
        goto addv;
    case TOK_DOTS:
        return strcpy(p, "...");
    case TOK_A_SHL:
        return strcpy(p, "<<=");
    case TOK_A_SAR:
        return strcpy(p, ">>=");
    case TOK_EOF:
        return strcpy(p, "<eof>");
    default:
        if (v < TOK_IDENT) {
            /* search in two bytes table */
            const unsigned char *q = tok_two_chars;
            while (*q) {
                if (q[2] == v) {
                    *p++ = q[0];
                    *p++ = q[1];
                    *p = '\0';
                    return cstr_buf.data;
                }
                q += 3;
            }
        if (v >= 127) {
            sprintf(cstr_buf.data, "<%02x>", v);
            return cstr_buf.data;
        }
        addv:
            *p++ = v;
            *p = '\0';
        } else if (v < tok_ident) {
            return table_ident[v - TOK_IDENT]->str;
        } else if (v >= SYM_FIRST_ANOM) {
            /* special name for anonymous symbol */
            sprintf(p, "L.%u", v - SYM_FIRST_ANOM);
        } else {
            /* should never happen */
            return NULL;
        }
        break;
    }
    return cstr_buf.data;
}

/* return the current character, handling end of block if necessary
   (but not stray) */
ST_FUNC int handle_eob(void)
{
    BufferedFile *bf = file;
    int len;

    /* only tries to read if really end of buffer */
    if (bf->buf_ptr >= bf->buf_end) {
        if (bf->fd >= 0) {
#if defined(PARSE_DEBUG)
            len = 1;
#else
            len = IO_BUF_SIZE;
#endif
            len = read(bf->fd, bf->buffer, len);
            if (len < 0)
                len = 0;
        } else {
            len = 0;
        }
        total_bytes += len;
        bf->buf_ptr = bf->buffer;
        bf->buf_end = bf->buffer + len;
        *bf->buf_end = CH_EOB;
    }
    if (bf->buf_ptr < bf->buf_end) {
        return bf->buf_ptr[0];
    } else {
        bf->buf_ptr = bf->buf_end;
        return CH_EOF;
    }
}

/* read next char from current input file and handle end of input buffer */
ST_INLN void inp(void)
{
    ch = *(++(file->buf_ptr));
    /* end of buffer/file handling */
    if (ch == CH_EOB)
        ch = handle_eob();
}

/* handle '\[\r]\n' */
static int handle_stray_noerror(void)
{
    while (ch == '\\') {
        inp();
        if (ch == '\n') {
            file->line_num++;
            inp();
        } else if (ch == '\r') {
            inp();
            if (ch != '\n')
                goto fail;
            file->line_num++;
            inp();
        } else {
        fail:
            return 1;
        }
    }
    return 0;
}

static void handle_stray(void)
{
    if (handle_stray_noerror())
        tcc_error(-1, "stray '\\' in program");
}

/* skip the stray and handle the \\n case. Output an error if
   incorrect char after the stray */
static int handle_stray1(uint8_t *p)
{
    int c;

    file->buf_ptr = p;
    if (p >= file->buf_end) {
        c = handle_eob();
        if (c != '\\')
            return c;
        p = file->buf_ptr;
    }
    ch = *p;
    if (handle_stray_noerror()) {
        if (!(parse_flags & PARSE_FLAG_ACCEPT_STRAYS))
            tcc_error(-1, "stray '\\' in program");
        *--file->buf_ptr = '\\';
    }
    p = file->buf_ptr;
    c = *p;
    return c;
}

/* handle just the EOB case, but not stray */
#define PEEKC_EOB(c, p)\
{\
    p++;\
    c = *p;\
    if (c == '\\') {\
        file->buf_ptr = p;\
        c = handle_eob();\
        p = file->buf_ptr;\
    }\
}

/* handle the complicated stray case */
#define PEEKC(c, p)\
{\
    p++;\
    c = *p;\
    if (c == '\\') {\
        c = handle_stray1(p);\
        p = file->buf_ptr;\
    }\
}

/* input with '\[\r]\n' handling. Note that this function cannot
   handle other characters after '\', so you cannot call it inside
   strings or comments */
ST_FUNC void minp(void)
{
    inp();
    if (ch == '\\') 
        handle_stray();
}

/* single line C++ comments */
static uint8_t *parse_line_comment(uint8_t *p)
{
    int c;

    p++;
    for(;;) {
        c = *p;
    redo:
        if (c == '\n' || c == CH_EOF) {
            break;
        } else if (c == '\\') {
            file->buf_ptr = p;
            c = handle_eob();
            p = file->buf_ptr;
            if (c == '\\') {
                PEEKC_EOB(c, p);
                if (c == '\n') {
                    file->line_num++;
                    PEEKC_EOB(c, p);
                } else if (c == '\r') {
                    PEEKC_EOB(c, p);
                    if (c == '\n') {
                        file->line_num++;
                        PEEKC_EOB(c, p);
                    }
                }
            } else {
                goto redo;
            }
        } else {
            p++;
        }
    }
    return p;
}

/* C comments */
ST_FUNC uint8_t *parse_comment(uint8_t *p)
{
    int c;

    p++;
    for(;;) {
        /* fast skip loop */
        for(;;) {
            c = *p;
            if (c == '\n' || c == '*' || c == '\\')
                break;
            p++;
            c = *p;
            if (c == '\n' || c == '*' || c == '\\')
                break;
            p++;
        }
        /* now we can handle all the cases */
        if (c == '\n') {
            file->line_num++;
            p++;
        } else if (c == '*') {
            p++;
            for(;;) {
                c = *p;
                if (c == '*') {
                    p++;
                } else if (c == '/') {
                    goto end_of_comment;
                } else if (c == '\\') {
                    file->buf_ptr = p;
                    c = handle_eob();
                    p = file->buf_ptr;
                    if( c == CH_EOF )  tcc_error(-1, "unexpected end of file in comment");
                    if (c == '\\') {
                        /* skip '\[\r]\n', otherwise just skip the stray */
                        while (c == '\\') {
                            PEEKC_EOB(c, p);
                            if (c == '\n') {
                                file->line_num++;
                                PEEKC_EOB(c, p);
                            } else if (c == '\r') {
                                PEEKC_EOB(c, p);
                                if (c == '\n') {
                                    file->line_num++;
                                    PEEKC_EOB(c, p);
                                }
                            } else {
                                goto after_star;
                            }
                        }
                    }
                } else {
                    break;
                }
            }
        after_star: ;
        }
        else {
            /* stray, eob or eof */
            file->buf_ptr = p;
            c = handle_eob();
            p = file->buf_ptr;
            if( c == CH_EOF ) tcc_error(-1, "unexpected end of file in comment");
            else if( c == '\\' ) p++;
        }
    }
 end_of_comment:
    p++;
    return p;
}

ST_FUNC int set_idnum(int c, int val)
{
    int prev = isidnum_table[c - CH_EOF];
    isidnum_table[c - CH_EOF] = val;
    return prev;
}

#define cinp minp

static inline void skip_spaces(void)
{
    while (isidnum_table[ch - CH_EOF] & IS_SPC)
        cinp();
}

static inline int check_space(int t, int *spc) 
{
    if (t < 256 && (isidnum_table[t - CH_EOF] & IS_SPC)) {
        if (*spc) 
            return 1;
        *spc = 1;
    } else 
        *spc = 0;
    return 0;
}

/* parse a string without interpreting escapes */
static uint8_t *parse_pp_string(uint8_t *p,
                                int sep, CString *str)
{
    int c;
    p++;
    for(;;) {
        c = *p;
        if (c == sep) {
            break;
        } else if (c == '\\') {
            file->buf_ptr = p;
            c = handle_eob();
            p = file->buf_ptr;
            if (c == CH_EOF) {
            unterminated_string:
                /* XXX: indicate line number of start of string */
                tcc_error(-1, "missing terminating %c character", sep);
            } else if (c == '\\') {
                /* escape : just skip \[\r]\n */
                PEEKC_EOB(c, p);
                if (c == '\n') {
                    file->line_num++;
                    p++;
                } else if (c == '\r') {
                    PEEKC_EOB(c, p);
                    if( c != '\n' ) tcc_error(-1, "'\n' after '\r' expected" );
                    file->line_num++;
                    p++;
                } else if (c == CH_EOF) {
                    goto unterminated_string;
                } else {
                    if (str) {
                        cstr_ccat(str, '\\');
                        cstr_ccat(str, c);
                    }
                    p++;
                }
            }
        } else if (c == '\n') {
            file->line_num++;
            goto add_char;
        } else if (c == '\r') {
            PEEKC_EOB(c, p);
            if (c != '\n') {
                if (str)
                    cstr_ccat(str, '\r');
            } else {
                file->line_num++;
                goto add_char;
            }
        } else {
        add_char:
            if (str)
                cstr_ccat(str, c);
            p++;
        }
    }
    p++;
    return p;
}

/* skip block of text until #else, #elif or #endif. skip also pairs of
   #if/#endif */
static void preprocess_skip(void)
{
    int a, start_of_line, c, in_warn_or_error;
    uint8_t *p;

    p = file->buf_ptr;
    a = 0;
redo_start:
    start_of_line = 1;
    in_warn_or_error = 0;
    for(;;) {
    redo_no_start:
        c = *p;
        switch(c) {
        case ' ':
        case '\t':
        case '\f':
        case '\v':
        case '\r':
            p++;
            goto redo_no_start;
        case '\n':
            file->line_num++;
            p++;
            goto redo_start;
        case '\\':
            file->buf_ptr = p;
            c = handle_eob();
            if( c == CH_EOF ) tcc_error(-1, "#endif expected" );
            else if (c == '\\') {
                ch = file->buf_ptr[0];
                handle_stray_noerror();
            }
            p = file->buf_ptr;
            goto redo_no_start;
        /* skip strings */
        case '\"':
        case '\'':
            if (in_warn_or_error)
                goto _default;
            p = parse_pp_string(p, c, NULL);
            break;
        /* skip comments */
        case '/':
            if (in_warn_or_error)
                goto _default;
            file->buf_ptr = p;
            ch = *p;
            minp();
            p = file->buf_ptr;
            if (ch == '*') {
                p = parse_comment(p);
            } else if (ch == '/') {
                p = parse_line_comment(p);
            }
            break;
        case '#':
            p++;
            if (start_of_line) {
                file->buf_ptr = p;
                next_nomacro();
                p = file->buf_ptr;
                if (a == 0 && 
                    (tok == TOK_ELSE || tok == TOK_ELIF || tok == TOK_ENDIF))
                    goto the_end;
                if (tok == TOK_IF || tok == TOK_IFDEF || tok == TOK_IFNDEF)
                    a++;
                else if (tok == TOK_ENDIF)
                    a--;
                else if( tok == TOK_ERROR || tok == TOK_WARNING)
                    in_warn_or_error = 1;
                else if (tok == TOK_LINEFEED)
                    goto redo_start;
                else if (parse_flags & PARSE_FLAG_ASM_FILE)
                    p = parse_line_comment(p - 1);
            } else if (parse_flags & PARSE_FLAG_ASM_FILE)
                p = parse_line_comment(p - 1);
            break;
_default:
        default:
            p++;
            break;
        }
        start_of_line = 0;
    }
 the_end: ;
    file->buf_ptr = p;
}

#if 0
/* return the number of additional 'ints' necessary to store the
   token */
static inline int tok_size(const int *p)
{
    switch(*p) {
        /* 4 bytes */
    case TOK_CINT:
    case TOK_CUINT:
    case TOK_CCHAR:
    case TOK_LCHAR:
    case TOK_CFLOAT:
    case TOK_LINENUM:
        return 1 + 1;
    case TOK_STR:
    case TOK_LSTR:
    case TOK_PPNUM:
    case TOK_PPSTR:
        return 1 + ((sizeof(CString) + ((CString *)(p+1))->size + 3) >> 2);
    case TOK_CLONG:
    case TOK_CULONG:
	return 1 + LONG_SIZE / 4;
    case TOK_CDOUBLE:
    case TOK_CLLONG:
    case TOK_CULLONG:
        return 1 + 2;
    case TOK_CLDOUBLE:
        return 1 + LDOUBLE_SIZE / 4;
    default:
        return 1 + 0;
    }
}
#endif

/* token string handling */
ST_INLN void tok_str_new(TokenString *s)
{
    s->str = NULL;
    s->len = s->lastlen = 0;
    s->allocated_len = 0;
    s->last_line_num = -1;
}

ST_FUNC TokenString *tok_str_alloc(void)
{
    TokenString *str = tal_realloc(tokstr_alloc, 0, sizeof *str);
    tok_str_new(str);
    return str;
}

ST_FUNC int *tok_str_dup(TokenString *s)
{
    int *str;

    str = tal_realloc(tokstr_alloc, 0, s->len * sizeof(int));
    memcpy(str, s->str, s->len * sizeof(int));
    return str;
}

ST_FUNC void tok_str_free_str(int *str)
{
    tal_free(tokstr_alloc, str);
}

ST_FUNC void tok_str_free(TokenString *str)
{
    tok_str_free_str(str->str);
    tal_free(tokstr_alloc, str);
}

ST_FUNC int *tok_str_realloc(TokenString *s, int new_size)
{
    int *str, size;

    size = s->allocated_len;
    if (size < 16)
        size = 16;
    while (size < new_size)
        size = size * 2;
    if (size > s->allocated_len) {
        str = tal_realloc(tokstr_alloc, s->str, size * sizeof(int));
        s->allocated_len = size;
        s->str = str;
    }
    return s->str;
}

ST_FUNC void tok_str_add(TokenString *s, int t)
{
    int len, *str;

    len = s->len;
    str = s->str;
    if (len >= s->allocated_len)
        str = tok_str_realloc(s, len + 1);
    str[len++] = t;
    s->len = len;
}

ST_FUNC void begin_macro(TokenString *str, int alloc)
{
    str->alloc = alloc;
    str->prev = macro_stack;
    str->prev_ptr = macro_ptr;
    str->save_line_num = file->line_num;
    macro_ptr = str->str;
    macro_stack = str;
}

ST_FUNC void end_macro(void)
{
    TokenString *str = macro_stack;
    macro_stack = str->prev;
    macro_ptr = str->prev_ptr;
    file->line_num = str->save_line_num;
    if (str->alloc == 2) {
        str->alloc = 3; /* just mark as finished */
    } else {
        tok_str_free(str);
    }
}

static void tok_str_add2(TokenString *s, int t, CValue *cv)
{
    int len, *str;

    len = s->lastlen = s->len;
    str = s->str;

    /* allocate space for worst case */
    if (len + TOK_MAX_SIZE >= s->allocated_len)
        str = tok_str_realloc(s, len + TOK_MAX_SIZE + 1);
    str[len++] = t;
    switch(t) {
    case TOK_CINT:
    case TOK_CUINT:
    case TOK_CCHAR:
    case TOK_LCHAR:
    case TOK_CFLOAT:
    case TOK_LINENUM:
#if LONG_SIZE == 4
    case TOK_CLONG:
    case TOK_CULONG:
#endif
        str[len++] = cv->tab[0];
        break;
    case TOK_PPNUM:
    case TOK_PPSTR:
    case TOK_STR:
    case TOK_LSTR:
        {
            /* Insert the string into the int array. */
            size_t nb_words =
                1 + (cv->str.size + sizeof(int) - 1) / sizeof(int);
            if (len + nb_words >= s->allocated_len)
                str = tok_str_realloc(s, len + nb_words + 1);
            str[len] = cv->str.size;
            memcpy(&str[len + 1], cv->str.data, cv->str.size);
            len += nb_words;
        }
        break;
    case TOK_CDOUBLE:
    case TOK_CLLONG:
    case TOK_CULLONG:
#if LONG_SIZE == 8
    case TOK_CLONG:
    case TOK_CULONG:
#endif
#if LDOUBLE_SIZE == 8
    case TOK_CLDOUBLE:
#endif
        str[len++] = cv->tab[0];
        str[len++] = cv->tab[1];
        break;
#if LDOUBLE_SIZE == 12
    case TOK_CLDOUBLE:
        str[len++] = cv->tab[0];
        str[len++] = cv->tab[1];
        str[len++] = cv->tab[2];
#elif LDOUBLE_SIZE == 16
    case TOK_CLDOUBLE:
        str[len++] = cv->tab[0];
        str[len++] = cv->tab[1];
        str[len++] = cv->tab[2];
        str[len++] = cv->tab[3];
#elif LDOUBLE_SIZE != 8
#error add long double size support
#endif
        break;
    default:
        break;
    }
    s->len = len;
}

/* add the current parse token in token string 's' */
ST_FUNC void tok_str_add_tok(TokenString *s)
{
    CValue cval;

    /* save line number info */
    if (file->line_num != s->last_line_num) {
        s->last_line_num = file->line_num;
        cval.i = s->last_line_num;
        tok_str_add2(s, TOK_LINENUM, &cval);
    }
    tok_str_add2(s, tok, &tokc);
}

/* get a token from an integer array and increment pointer
   accordingly. we code it as a macro to avoid pointer aliasing. */
static inline void TOK_GET(int *t, const int **pp, CValue *cv)
{
    const int *p = *pp;
    int n, *tab;

    tab = cv->tab;
    switch(*t = *p++) {
#if LONG_SIZE == 4
    case TOK_CLONG:
#endif
    case TOK_CINT:
    case TOK_CCHAR:
    case TOK_LCHAR:
    case TOK_LINENUM:
        cv->i = *p++;
        break;
#if LONG_SIZE == 4
    case TOK_CULONG:
#endif
    case TOK_CUINT:
        cv->i = (unsigned)*p++;
        break;
    case TOK_CFLOAT:
	tab[0] = *p++;
	break;
    case TOK_STR:
    case TOK_LSTR:
    case TOK_PPNUM:
    case TOK_PPSTR:
        cv->str.size = *p++;
        cv->str.data = p;
        p += (cv->str.size + sizeof(int) - 1) / sizeof(int);
        break;
    case TOK_CDOUBLE:
    case TOK_CLLONG:
    case TOK_CULLONG:
#if LONG_SIZE == 8
    case TOK_CLONG:
    case TOK_CULONG:
#endif
        n = 2;
        goto copy;
    case TOK_CLDOUBLE:
#if LDOUBLE_SIZE == 16
        n = 4;
#elif LDOUBLE_SIZE == 12
        n = 3;
#elif LDOUBLE_SIZE == 8
        n = 2;
#else
# error add long double size support
#endif
    copy:
        do
            *tab++ = *p++;
        while (--n);
        break;
    default:
        break;
    }
    *pp = p;
}

static int macro_is_equal(const int *a, const int *b)
{
    CValue cv;
    int t;

    if (!a || !b)
        return 1;

    while (*a && *b) {
        /* first time preallocate macro_equal_buf, next time only reset position to start */
        cstr_reset(&macro_equal_buf);
        TOK_GET(&t, &a, &cv);
        cstr_cat(&macro_equal_buf, get_tok_str(t, &cv), 0);
        TOK_GET(&t, &b, &cv);
        if (strcmp(macro_equal_buf.data, get_tok_str(t, &cv)))
            return 0;
    }
    return !(*a || *b);
}

/* defines handling */
ST_INLN void define_push(int v, int macro_type, int *str, Sym *first_arg)
{
    Sym *s, *o;

    o = define_find(v);
    s = sym_push2(&define_stack, v, macro_type, 0);
    s->d = str;
    s->next = first_arg;
    table_ident[v - TOK_IDENT]->sym_define = s;

    if (o && !macro_is_equal(o->d, s->d))
	tcc_error(0, "%s redefined", get_tok_str(v, NULL));
}

/* undefined a define symbol. Its name is just set to zero */
ST_FUNC void define_undef(Sym *s)
{
    int v = s->v;
    if (v >= TOK_IDENT && v < tok_ident)
        table_ident[v - TOK_IDENT]->sym_define = NULL;
}

ST_INLN Sym *define_find(int v)
{
    v -= TOK_IDENT;
    if ((unsigned)v >= (unsigned)(tok_ident - TOK_IDENT))
        return NULL;
    return table_ident[v]->sym_define;
}

/* free define stack until top reaches 'b' */
ST_FUNC void free_defines(Sym *b)
{
    while (define_stack != b) {
        Sym *top = define_stack;
        define_stack = top->prev;
        tok_str_free_str(top->d);
        define_undef(top);
        sym_free(top);
    }

    /* restore remaining (-D or predefined) symbols if they were
       #undef'd in the file */
    while (b) {
        int v = b->v;
        if (v >= TOK_IDENT && v < tok_ident) {
            Sym **d = &table_ident[v - TOK_IDENT]->sym_define;
            if (!*d)
                *d = b;
        }
        b = b->prev;
    }
}

/* label lookup */
ST_FUNC Sym *label_find(int v)
{
    v -= TOK_IDENT;
    if ((unsigned)v >= (unsigned)(tok_ident - TOK_IDENT))
        return NULL;
    return table_ident[v]->sym_label;
}

ST_FUNC Sym *label_push(Sym **ptop, int v, int flags)
{
    Sym *s, **ps;
    s = sym_push2(ptop, v, 0, 0);
    s->r = flags;
    ps = &table_ident[v - TOK_IDENT]->sym_label;
    if (ptop == &global_label_stack) {
        /* modify the top most local identifier, so that
           sym_identifier will point to 's' when popped */
        while (*ps != NULL)
            ps = &(*ps)->prev_tok;
    }
    s->prev_tok = *ps;
    *ps = s;
    return s;
}

/* pop labels until element last is reached. Look if any labels are
   undefined. Define symbols if '&&label' was used. */
ST_FUNC void label_pop(Sym **ptop, Sym *slast, int keep)
{
    Sym *s, *s1;
    for(s = *ptop; s != slast; s = s1) {
        s1 = s->prev;
        if (s->r == LABEL_DECLARED) {
            tcc_error(0, "label '%s' declared but not used", get_tok_str(s->v, NULL));
        } else if (s->r == LABEL_FORWARD) {
                tcc_error(-1, "label '%s' used but not defined",
                      get_tok_str(s->v, NULL));
        } else {
            if (s->c) {
                /* define corresponding symbol. A size of
                   1 is put. */
                put_extern_sym(s, cur_text_section, s->jnext, 1);
            }
        }
        /* remove label */
        table_ident[s->v - TOK_IDENT]->sym_label = s->prev_tok;
        if (!keep)
            sym_free(s);
    }
    if (!keep)
        *ptop = slast;
}

/* eval an expression for #if/#elif */
static int expr_preprocess(void)
{
    int c, t;
    TokenString *str;
    
    str = tok_str_alloc();
    pp_expr = 1;
    while (tok != TOK_LINEFEED && tok != TOK_EOF) {
        next(); /* do macro subst */
        if (tok == TOK_DEFINED) {
            next_nomacro();
            t = tok;
            if( t == '(' ) next_nomacro();
            if( tok < TOK_IDENT )  tcc_error(-1, "identifier expected" );
            c = define_find(tok) != 0;
            if (t == '(') {
                next_nomacro();
                if( tok != ')' )  tcc_error(-1, "')' expected" );
            }
            tok = TOK_CINT;
            tokc.i = c;
        } else if (tok >= TOK_IDENT) {
            /* if undefined macro */
            tok = TOK_CINT;
            tokc.i = 0;
        }
        tok_str_add_tok(str);
    }
    pp_expr = 0;
    tok_str_add(str, -1); /* simulate end of file */
    tok_str_add(str, 0);
    /* now evaluate C constant expression */
    begin_macro(str, 1);
    next();
    c = expr_const();
    end_macro();
    return c != 0;
}


/* parse after #define */
ST_FUNC void parse_define(void)
{
    Sym *s, *first, **ps;
    int v, t, varg, is_vaargs, spc;
    int saved_parse_flags = parse_flags;

    v = tok;
    if (v < TOK_IDENT || v == TOK_DEFINED)
        tcc_error(-1, "invalid macro name '%s'", get_tok_str(tok, &tokc));
    /* XXX: should check if same macro (ANSI) */
    first = NULL;
    t = MACRO_OBJ;
    /* We have to parse the whole define as if not in asm mode, in particular
       no line comment with '#' must be ignored.  Also for function
       macros the argument list must be parsed without '.' being an ID
       character.  */
    parse_flags = ((parse_flags & ~PARSE_FLAG_ASM_FILE) | PARSE_FLAG_SPACES);
    /* '(' must be just after macro definition for MACRO_FUNC */
    next_nomacro_spc();
    if (tok == '(') {
        int dotid = set_idnum('.', 0);
        next_nomacro();
        ps = &first;
        if (tok != ')') for (;;) {
            varg = tok;
            next_nomacro();
            is_vaargs = 0;
            if (varg == TOK_DOTS) {
                varg = TOK___VA_ARGS__;
                is_vaargs = 1;
            } else if (tok == TOK_DOTS && gnu_ext) {
                is_vaargs = 1;
                next_nomacro();
            }
            if (varg < TOK_IDENT)
        bad_list:
                tcc_error(-1, "bad macro parameter list");
            s = sym_push2(&define_stack, varg | SYM_FIELD, is_vaargs, 0);
            *ps = s;
            ps = &s->next;
            if (tok == ')')
                break;
            if (tok != ',' || is_vaargs)
                goto bad_list;
            next_nomacro();
        }
        next_nomacro_spc();
        t = MACRO_FUNC;
        set_idnum('.', dotid);
    }

    tokstr_buf.len = 0;
    spc = 2;
    parse_flags |= PARSE_FLAG_ACCEPT_STRAYS | PARSE_FLAG_SPACES | PARSE_FLAG_LINEFEED;
    /* The body of a macro definition should be parsed such that identifiers
       are parsed like the file mode determines (i.e. with '.' being an
       ID character in asm mode).  But '#' should be retained instead of
       regarded as line comment leader, so still don't set ASM_FILE
       in parse_flags. */
    while (tok != TOK_LINEFEED && tok != TOK_EOF) {
        /* remove spaces around ## and after '#' */
        if (TOK_TWOSHARPS == tok) {
            if (2 == spc)
                goto bad_twosharp;
            if (1 == spc)
                --tokstr_buf.len;
            spc = 3;
	    tok = TOK_PPJOIN;
        } else if ('#' == tok) {
            spc = 4;
        } else if (check_space(tok, &spc)) {
            goto skip;
        }
        tok_str_add2(&tokstr_buf, tok, &tokc);
    skip:
        next_nomacro_spc();
    }

    parse_flags = saved_parse_flags;
    if (spc == 1)
        --tokstr_buf.len; /* remove trailing space */
    tok_str_add(&tokstr_buf, 0);
    if (3 == spc)
bad_twosharp:
        tcc_error(-1, "'##' cannot appear at either end of macro");
    define_push(v, t, tok_str_dup(&tokstr_buf), first);
}

static CachedInclude *search_cached_include(TCCState *s1, const char *filename, int add)
{
    const unsigned char *s;
    unsigned int h;
    CachedInclude *e;
    int i;

    h = TOK_HASH_INIT;
    s = (unsigned char *) filename;
    while (*s) {
#ifdef _WIN32
        h = TOK_HASH_FUNC(h, toup(*s));
#else
        h = TOK_HASH_FUNC(h, *s);
#endif
        s++;
    }
    h &= (CACHED_INCLUDES_HASH_SIZE - 1);

    i = s1->cached_includes_hash[h];
    for(;;) {
        if (i == 0)
            break;
        e = s1->cached_includes[i - 1];
        if (0 == PATHCMP(e->filename, filename))
            return e;
        i = e->hash_next;
    }
    if (!add)
        return NULL;

    e = tcc_malloc(sizeof(CachedInclude) + strlen(filename));
    strcpy(e->filename, filename);
    e->ifndef_macro = e->once = 0;
    dynarray_add(&s1->cached_includes, &s1->nb_cached_includes, e);
    /* add in hash table */
    e->hash_next = s1->cached_includes_hash[h];
    s1->cached_includes_hash[h] = s1->nb_cached_includes;
#ifdef INC_DEBUG
    printf("adding cached '%s'\n", filename);
#endif
    return e;
}

static void pragma_parse(TCCState *s1)
{
    next_nomacro();
    if (tok == TOK_push_macro || tok == TOK_pop_macro) {
        int t = tok, v;
        Sym *s;

        if (next(), tok != '(')
            goto pragma_err;
        if (next(), tok != TOK_STR)
            goto pragma_err;
        v = tok_alloc(tokc.str.data, tokc.str.size - 1)->tok;
        if (next(), tok != ')')
            goto pragma_err;
        if (t == TOK_push_macro) {
            while (NULL == (s = define_find(v)))
                define_push(v, 0, NULL, NULL);
            s->type.ref = s; /* set push boundary */
        } else {
            for (s = define_stack; s; s = s->prev)
                if (s->v == v && s->type.ref == s) {
                    s->type.ref = NULL;
                    break;
                }
        }
        if (s)
            table_ident[v - TOK_IDENT]->sym_define = s->d ? s : NULL;
        else
            tcc_error(0, "unbalanced #pragma pop_macro");
        pp_debug_tok = t, pp_debug_symv = v;

    } else if (tok == TOK_once) {
        search_cached_include(s1, file->filename, 1)->once = pp_once;

    } else if (tok == TOK_pack) {
        /* This may be:
           #pragma pack(1) // set
           #pragma pack() // reset to default
           #pragma pack(push,1) // push & set
           #pragma pack(pop) // restore previous */
        next();
        skip('(');
        if (tok == TOK_ASM_pop) {
            next();
            if (s1->pack_stack_ptr <= s1->pack_stack) {
            stk_error:
                tcc_error(-1, "out of pack stack");
            }
            s1->pack_stack_ptr--;
        } else {
            int val = 0;
            if (tok != ')') {
                if (tok == TOK_ASM_push) {
                    next();
                    if (s1->pack_stack_ptr >= s1->pack_stack + PACK_STACK_SIZE - 1)
                        goto stk_error;
                    s1->pack_stack_ptr++;
                    skip(',');
                }
                if (tok != TOK_CINT)
                    goto pragma_err;
                val = tokc.i;
                if (val < 1 || val > 16 || (val & (val - 1)) != 0)
                    goto pragma_err;
                next();
            }
            *s1->pack_stack_ptr = val;
        }
        if (tok != ')')
            goto pragma_err;

    } else if (tok == TOK_comment) {
        char *p; int t;
        next();
        skip('(');
        t = tok;
        next();
        skip(',');
        if (tok != TOK_STR)
            goto pragma_err;
        p = tcc_strdup((char *)tokc.str.data);
        next();
        if (tok != ')')
            goto pragma_err;
        if (t == TOK_lib) {
            dynarray_add(&s1->pragma_libs, &s1->nb_pragma_libs, p);
        } else {
            if (t == TOK_option)
                tcc_set_options(s1, p);
            tcc_free(p);
        }

    } else if (s1->warn_unsupported) {
        tcc_error(0, "#pragma %s is ignored", get_tok_str(tok, &tokc));
    }
    return;

pragma_err:
    tcc_error(-1, "malformed #pragma directive");
    return;
}

/* is_bof is true if first non space token at beginning of file */
ST_FUNC void preprocess(int is_bof)
{
    TCCState *s1 = tcc_state;
    int i, c, n, saved_parse_flags;
    char buf[1024], *q;
    Sym *s;

    saved_parse_flags = parse_flags;
    parse_flags = PARSE_FLAG_PREPROCESS
        | PARSE_FLAG_TOK_NUM
        | PARSE_FLAG_TOK_STR
        | PARSE_FLAG_LINEFEED
        | (parse_flags & PARSE_FLAG_ASM_FILE)
        ;

    next_nomacro();
 redo:
    switch(tok) {
    case TOK_DEFINE:
        pp_debug_tok = tok;
        next_nomacro();
        pp_debug_symv = tok;
        parse_define();
        break;
    case TOK_UNDEF:
        pp_debug_tok = tok;
        next_nomacro();
        pp_debug_symv = tok;
        s = define_find(tok);
        /* undefine symbol by putting an invalid name */
        if (s)
            define_undef(s);
        break;
    case TOK_INCLUDE:
    case TOK_INCLUDE_NEXT:
        ch = file->buf_ptr[0];
        /* XXX: incorrect if comments : use next_nomacro with a special mode */
        skip_spaces();
        if (ch == '<') {
            c = '>';
            goto read_name;
        } else if (ch == '\"') {
            c = ch;
        read_name:
            inp();
            q = buf;
            while (ch != c && ch != '\n' && ch != CH_EOF) {
                if ((q - buf) < sizeof(buf) - 1)
                    *q++ = ch;
                if (ch == '\\') {
                    if (handle_stray_noerror() == 0)
                        --q;
                } else
                    inp();
            }
            *q = '\0';
            minp();
        } else {
	    int len;
            /* computed #include : concatenate everything up to linefeed,
	       the result must be one of the two accepted forms.
	       Don't convert pp-tokens to tokens here.  */
	    parse_flags = (PARSE_FLAG_PREPROCESS
			   | PARSE_FLAG_LINEFEED
			   | (parse_flags & PARSE_FLAG_ASM_FILE));
            next();
            buf[0] = '\0';
	    while (tok != TOK_LINEFEED) {
		pstrcat(buf, sizeof(buf), get_tok_str(tok, &tokc));
		next();
	    }
	    len = strlen(buf);
	    /* check syntax and remove '<>|""' */
	    if ((len < 2 || ((buf[0] != '"' || buf[len-1] != '"') &&
			     (buf[0] != '<' || buf[len-1] != '>'))))
	        tcc_error(-1, "'#include' expects \"FILENAME\" or <FILENAME>");
	    c = buf[len-1];
	    memmove(buf, buf + 1, len - 2);
	    buf[len - 2] = '\0';
        }

        if (s1->include_stack_ptr >= s1->include_stack + INCLUDE_STACK_SIZE)
            tcc_error(-1, "#include recursion too deep");
        /* store current file in stack, but increment stack later below */
        *s1->include_stack_ptr = file;
        i = tok == TOK_INCLUDE_NEXT ? file->include_next_index : 0;
        n = 2 + s1->nb_include_paths + s1->nb_sysinclude_paths;
        for (; i < n; ++i) {
            char buf1[sizeof file->filename];
            CachedInclude *e;
            const char *path;

            if (i == 0) {
                /* check absolute include path */
                if (!IS_ABSPATH(buf))
                    continue;
                buf1[0] = 0;

            } else if (i == 1) {
                /* search in file's dir if "header.h" */
                if (c != '\"')
                    continue;
                /* https://savannah.nongnu.org/bugs/index.php?50847 */
                path = file->true_filename;
                pstrncpy(buf1, path, tcc_basename(path) - path);

            } else {
                /* search in all the include paths */
                int j = i - 2, k = j - s1->nb_include_paths;
                path = k < 0 ? s1->include_paths[j] : s1->sysinclude_paths[k];
                pstrcpy(buf1, sizeof(buf1), path);
                pstrcat(buf1, sizeof(buf1), "/");
            }

            pstrcat(buf1, sizeof(buf1), buf);
            e = search_cached_include(s1, buf1, 0);
            if (e && (define_find(e->ifndef_macro) || e->once == pp_once)) {
                /* no need to parse the include because the 'ifndef macro'
                   is defined (or had #pragma once) */
#ifdef INC_DEBUG
                printf("%s: skipping cached %s\n", file->filename, buf1);
#endif
                goto include_done;
            }

            if (tcc_open(s1, buf1) < 0)
                continue;

            file->include_next_index = i + 1;
#ifdef INC_DEBUG
            printf("%s: including %s\n", file->prev->filename, file->filename);
#endif
            /* update target deps */
            dynarray_add(&s1->target_deps, &s1->nb_target_deps,
                    tcc_strdup(buf1));
            /* push current file in stack */
            ++s1->include_stack_ptr;
#if defined CONFIG_TCC_GDEBUG
            /* add include file debug info */
            if( s1->do_debug )  put_stabs(file->filename, N_BINCL, 0, 0, 0);
#endif
            tok_flags |= TOK_FLAG_BOF | TOK_FLAG_BOL;
            ch = file->buf_ptr[0];
            goto the_end;
        }
        tcc_error(-1, "include file '%s' not found", buf);
include_done:
        break;
    case TOK_IFNDEF:
        c = 1;
        goto do_ifdef;
    case TOK_IF:
        c = expr_preprocess();
        goto do_if;
    case TOK_IFDEF:
        c = 0;
    do_ifdef:
        next_nomacro();
        if (tok < TOK_IDENT)
            tcc_error(-1, "invalid argument for '#if%sdef'", c ? "n" : "");
        if (is_bof) {
            if (c) {
#ifdef INC_DEBUG
                printf("#ifndef %s\n", get_tok_str(tok, NULL));
#endif
                file->ifndef_macro = tok;
            }
        }
        c = (define_find(tok) != 0) ^ c;
    do_if:
        if (s1->ifdef_stack_ptr >= s1->ifdef_stack + IFDEF_STACK_SIZE)
            tcc_error(-1, "memory full (ifdef)");
        *s1->ifdef_stack_ptr++ = c;
        goto test_skip;
    case TOK_ELSE:
        if (s1->ifdef_stack_ptr == s1->ifdef_stack)
            tcc_error(-1, "#else without matching #if");
        if (s1->ifdef_stack_ptr[-1] & 2)
            tcc_error(-1, "#else after #else");
        c = (s1->ifdef_stack_ptr[-1] ^= 3);
        goto test_else;
    case TOK_ELIF:
        if (s1->ifdef_stack_ptr == s1->ifdef_stack)
            tcc_error(-1, "#elif without matching #if");
        c = s1->ifdef_stack_ptr[-1];
        if( c > 1 )  tcc_error(-1, "#elif after #else");
        /* last #if/#elif expression was true: we skip */
        if (c == 1) {
            c = 0;
        } else {
            c = expr_preprocess();
            s1->ifdef_stack_ptr[-1] = c;
        }
    test_else:
        if (s1->ifdef_stack_ptr == file->ifdef_stack_ptr + 1)
            file->ifndef_macro = 0;
    test_skip:
        if (!(c & 1)) {
            preprocess_skip();
            is_bof = 0;
            goto redo;
        }
        break;
    case TOK_ENDIF:
        if (s1->ifdef_stack_ptr <= file->ifdef_stack_ptr)
            tcc_error(-1, "#endif without matching #if");
        s1->ifdef_stack_ptr--;
        /* '#ifndef macro' was at the start of file. Now we check if
           an '#endif' is exactly at the end of file */
        if (file->ifndef_macro &&
            s1->ifdef_stack_ptr == file->ifdef_stack_ptr) {
            file->ifndef_macro_saved = file->ifndef_macro;
            /* need to set to zero to avoid false matches if another
               #ifndef at middle of file */
            file->ifndef_macro = 0;
            while (tok != TOK_LINEFEED)
                next_nomacro();
            tok_flags |= TOK_FLAG_ENDIF;
            goto the_end;
        }
        break;
    case TOK_PPNUM:
        n = strtoul((char*)tokc.str.data, &q, 10);
        goto _line_num;
    case TOK_LINE:
        next();
        if (tok != TOK_CINT)
    _line_err:
            tcc_error(-1, "wrong #line format");
        n = tokc.i;
    _line_num:
        next();
        if (tok != TOK_LINEFEED) {
            if (tok == TOK_STR) {
                if (file->true_filename == file->filename)
                    file->true_filename = tcc_strdup(file->filename);
                pstrcpy(file->filename, sizeof(file->filename), (char *)tokc.str.data);
            } else if (parse_flags & PARSE_FLAG_ASM_FILE)
                break;
            else
                goto _line_err;
            --n;
        }
        if (file->fd > 0)
            total_lines += file->line_num - n;
        file->line_num = n;
#if defined CONFIG_TCC_GDEBUG
        if( s1->do_debug )  put_stabs(file->filename, N_BINCL, 0, 0, 0);
#endif
        break;
    case TOK_ERROR:
    case TOK_WARNING:
        c = tok;
        ch = file->buf_ptr[0];
        skip_spaces();
        q = buf;
        while (ch != '\n' && ch != CH_EOF) {
            if ((q - buf) < sizeof(buf) - 1)
                *q++ = ch;
            if (ch == '\\') {
                if (handle_stray_noerror() == 0)
                    --q;
            } else
                inp();
        }
        *q = '\0';
        if( c == TOK_ERROR )  tcc_error(-1, "#error %s", buf);
        else                  tcc_error(0, "#warning %s", buf);
        break;
    case TOK_PRAGMA:
        pragma_parse(s1);
        break;
    case TOK_LINEFEED:
        goto the_end;
    default:
        /* ignore gas line comment in an 'S' file. */
        if (saved_parse_flags & PARSE_FLAG_ASM_FILE)
            goto ignore;
        if (tok == '!' && is_bof)
            /* '!' is ignored at beginning to allow C scripts. */
            goto ignore;
        tcc_error(0, "Ignoring unknown preprocessing directive #%s", get_tok_str(tok, &tokc));
    ignore:
        file->buf_ptr = parse_line_comment(file->buf_ptr - 1);
        goto the_end;
    }
    /* ignore other preprocess commands or #! for C scripts */
    while (tok != TOK_LINEFEED)
        next_nomacro();
 the_end:
    parse_flags = saved_parse_flags;
}

/* evaluate escape codes in a string. */
static void parse_escape_string(CString *outstr, const uint8_t *buf, int is_long)
{
    int c, n;
    const uint8_t *p;

    p = buf;
    for(;;) {
        c = *p;
        if (c == '\0')
            break;
        if (c == '\\') {
            p++;
            /* escape */
            c = *p;
            switch(c) {
            case '0': case '1': case '2': case '3':
            case '4': case '5': case '6': case '7':
                /* at most three octal digits */
                n = c - '0';
                p++;
                c = *p;
                if (isoct(c)) {
                    n = n * 8 + c - '0';
                    p++;
                    c = *p;
                    if (isoct(c)) {
                        n = n * 8 + c - '0';
                        p++;
                    }
                }
                c = n;
                goto add_char_nonext;
            case 'x':
            case 'u':
            case 'U':
                p++;
                n = 0;
                for(;;) {
                    c = *p;
                    if (c >= 'a' && c <= 'f')
                        c = c - 'a' + 10;
                    else if (c >= 'A' && c <= 'F')
                        c = c - 'A' + 10;
                    else if (isnum(c))
                        c = c - '0';
                    else
                        break;
                    n = n * 16 + c;
                    p++;
                }
                c = n;
                goto add_char_nonext;
            case 'a':
                c = '\a';
                break;
            case 'b':
                c = '\b';
                break;
            case 'f':
                c = '\f';
                break;
            case 'n':
                c = '\n';
                break;
            case 'r':
                c = '\r';
                break;
            case 't':
                c = '\t';
                break;
            case 'v':
                c = '\v';
                break;
            case 'e':
                if (!gnu_ext)
                    goto invalid_escape;
                c = 27;
                break;
            case '\'':
            case '\"':
            case '\\': 
            case '?':
                break;
            default:
            invalid_escape:
                if( c >= '!' && c <= '~' )  tcc_error(0, "unknown escape sequence: \'\\%c\'", c);
                else  tcc_error(0, "unknown escape sequence: \'\\x%x\'", c);
                break;
            }
        } else if (is_long && c >= 0x80) {
            /* assume we are processing UTF-8 sequence */
            /* reference: The Unicode Standard, Version 10.0, ch3.9 */

            int cont; /* count of continuation bytes */
            int skip; /* how many bytes should skip when error occurred */
            int i;

            /* decode leading byte */
            if (c < 0xC2) {
	            skip = 1; goto invalid_utf8_sequence;
            } else if (c <= 0xDF) {
	            cont = 1; n = c & 0x1f;
            } else if (c <= 0xEF) {
	            cont = 2; n = c & 0xf;
            } else if (c <= 0xF4) {
	            cont = 3; n = c & 0x7;
            } else {
	            skip = 1; goto invalid_utf8_sequence;
            }

            /* decode continuation bytes */
            for (i = 1; i <= cont; i++) {
                int l = 0x80, h = 0xBF;

                /* adjust limit for second byte */
                if (i == 1) {
                    switch (c) {
                    case 0xE0: l = 0xA0; break;
                    case 0xED: h = 0x9F; break;
                    case 0xF0: l = 0x90; break;
                    case 0xF4: h = 0x8F; break;
                    }
                }

                if (p[i] < l || p[i] > h) {
                    skip = i; goto invalid_utf8_sequence;
                }

                n = (n << 6) | (p[i] & 0x3f);
            }

            /* advance pointer */
            p += 1 + cont;
            c = n;
            goto add_char_nonext;

            /* error handling */
        invalid_utf8_sequence:
            tcc_error(0, "ill-formed UTF-8 subsequence starting with: \'\\x%x\'", c);
            c = 0xFFFD;
            p += skip;
            goto add_char_nonext;

        }
        p++;
    add_char_nonext:
        if (!is_long)
            cstr_ccat(outstr, c);
        else {
#ifdef TCC_TARGET_PE
            /* store as UTF-16 */
            if (c < 0x10000) {
                cstr_wccat(outstr, c);
            } else {
                c -= 0x10000;
                cstr_wccat(outstr, (c >> 10) + 0xD800);
                cstr_wccat(outstr, (c & 0x3FF) + 0xDC00);
            }
#else
            cstr_wccat(outstr, c);
#endif
        }
    }
    /* add a trailing '\0' */
    if (!is_long)
        cstr_ccat(outstr, '\0');
    else
        cstr_wccat(outstr, '\0');
}

static void parse_string(const char *s, int len)
{
    uint8_t buf[1000], *p = buf;
    int is_long, sep;

    if ((is_long = *s == 'L'))
        ++s, --len;
    sep = *s++;
    len -= 2;
    if (len >= sizeof buf)
        p = tcc_malloc(len + 1);
    memcpy(p, s, len);
    p[len] = 0;

    cstr_reset(&tokcstr);
    parse_escape_string(&tokcstr, p, is_long);
    if (p != buf)
        tcc_free(p);

    if (sep == '\'') {
        int char_size, i, n, c;
        /* XXX: make it portable */
        if (!is_long)
            tok = TOK_CCHAR, char_size = 1;
        else
            tok = TOK_LCHAR, char_size = sizeof(nwchar_t);
        n = tokcstr.size / char_size - 1;
        if( n < 1 )  tcc_error(-1, "empty character constant");
        if( n > 1 )  tcc_error(0, "multi-character character constant");
        for (c = i = 0; i < n; ++i) {
            if (is_long)
                c = ((nwchar_t *)tokcstr.data)[i];
            else
                c = (c << 8) | ((char *)tokcstr.data)[i];
        }
        tokc.i = c;
    } else {
        tokc.str.size = tokcstr.size;
        tokc.str.data = tokcstr.data;
        if (!is_long)
            tok = TOK_STR;
        else
            tok = TOK_LSTR;
    }
}

/* we use 64 bit numbers */
#define BN_SIZE 2

/* bn = (bn << shift) | or_val */
static void bn_lshift(unsigned int *bn, int shift, int or_val)
{
    int i;
    unsigned int v;
    for(i=0;i<BN_SIZE;i++) {
        v = bn[i];
        bn[i] = (v << shift) | or_val;
        or_val = v >> (32 - shift);
    }
}

static void bn_zero(unsigned int *bn)
{
    int i;
    for(i=0;i<BN_SIZE;i++) {
        bn[i] = 0;
    }
}

/* parse number in null terminated string 'p' and return it in the
   current token */
static void parse_number(const char *p)
{
    int b, t, shift, frac_bits, s, exp_val, ch;
    char *q;
    unsigned int bn[BN_SIZE];
    double d;

    /* number */
    q = token_buf;
    ch = *p++;
    t = ch;
    ch = *p++;
    *q++ = t;
    b = 10;
    if (t == '.') {
        goto float_frac_parse;
    } else if (t == '0') {
        if (ch == 'x' || ch == 'X') {
            q--;
            ch = *p++;
            b = 16;
        } else if (tcc_ext && (ch == 'b' || ch == 'B')) {
            q--;
            ch = *p++;
            b = 2;
        }
    }
    /* parse all digits. cannot check octal numbers at this stage
       because of floating point constants */
    while (1) {
        if (ch >= 'a' && ch <= 'f')
            t = ch - 'a' + 10;
        else if (ch >= 'A' && ch <= 'F')
            t = ch - 'A' + 10;
        else if (isnum(ch))
            t = ch - '0';
        else
            break;
        if (t >= b)
            break;
        if (q >= token_buf + STRING_MAX_SIZE) {
        num_too_long:
            tcc_error(-1, "number too long");
        }
        *q++ = ch;
        ch = *p++;
    }
    if (ch == '.' ||
        ((ch == 'e' || ch == 'E') && b == 10) ||
        ((ch == 'p' || ch == 'P') && (b == 16 || b == 2))) {
        if (b != 10) {
            /* NOTE: strtox should support that for hexa numbers, but
               non ISOC99 libcs do not support it, so we prefer to do
               it by hand */
            /* hexadecimal or binary floats */
            /* XXX: handle overflows */
            *q = '\0';
            if (b == 16)
                shift = 4;
            else 
                shift = 1;
            bn_zero(bn);
            q = token_buf;
            while (1) {
                t = *q++;
                if (t == '\0') {
                    break;
                } else if (t >= 'a') {
                    t = t - 'a' + 10;
                } else if (t >= 'A') {
                    t = t - 'A' + 10;
                } else {
                    t = t - '0';
                }
                bn_lshift(bn, shift, t);
            }
            frac_bits = 0;
            if (ch == '.') {
                ch = *p++;
                while (1) {
                    t = ch;
                    if (t >= 'a' && t <= 'f') {
                        t = t - 'a' + 10;
                    } else if (t >= 'A' && t <= 'F') {
                        t = t - 'A' + 10;
                    } else if (t >= '0' && t <= '9') {
                        t = t - '0';
                    } else {
                        break;
                    }
                    if( t >= b )  tcc_error(-1, "invalid digit");
                    bn_lshift(bn, shift, t);
                    frac_bits += shift;
                    ch = *p++;
                }
            }
            if( ch != 'p' && ch != 'P' )  tcc_error(-1, "exponent expected" );
            ch = *p++;
            s = 1;
            exp_val = 0;
            if (ch == '+') {
                ch = *p++;
            } else if (ch == '-') {
                s = -1;
                ch = *p++;
            }
            if( ch < '0' || ch > '9' )  tcc_error(-1, "exponent digits expected" );
            while (ch >= '0' && ch <= '9') {
                exp_val = exp_val * 10 + ch - '0';
                ch = *p++;
            }
            exp_val = exp_val * s;
            
            /* now we can generate the number */
            /* XXX: should patch directly float number */
            d = (double)bn[1] * 4294967296.0 + (double)bn[0];
            d = ldexp(d, exp_val - frac_bits);
            t = toup(ch);
            if (t == 'F') {
                ch = *p++;
                tok = TOK_CFLOAT;
                /* float : should handle overflow */
                tokc.f = (float)d;
            } else if (t == 'L') {
                ch = *p++;
#ifdef TCC_TARGET_PE
                tok = TOK_CDOUBLE;
                tokc.d = d;
#else
                tok = TOK_CLDOUBLE;
                /* XXX: not large enough */
                tokc.ld = (long double)d;
#endif
            } else {
                tok = TOK_CDOUBLE;
                tokc.d = d;
            }
        } else {
            /* decimal floats */
            if (ch == '.') {
                if (q >= token_buf + STRING_MAX_SIZE)
                    goto num_too_long;
                *q++ = ch;
                ch = *p++;
            float_frac_parse:
                while (ch >= '0' && ch <= '9') {
                    if (q >= token_buf + STRING_MAX_SIZE)
                        goto num_too_long;
                    *q++ = ch;
                    ch = *p++;
                }
            }
            if (ch == 'e' || ch == 'E') {
                if (q >= token_buf + STRING_MAX_SIZE)
                    goto num_too_long;
                *q++ = ch;
                ch = *p++;
                if (ch == '-' || ch == '+') {
                    if (q >= token_buf + STRING_MAX_SIZE)
                        goto num_too_long;
                    *q++ = ch;
                    ch = *p++;
                }
                if( ch < '0' || ch > '9' )  tcc_error(-1, "exponent digits expected" );
                while (ch >= '0' && ch <= '9') {
                    if (q >= token_buf + STRING_MAX_SIZE)
                        goto num_too_long;
                    *q++ = ch;
                    ch = *p++;
                }
            }
            *q = '\0';
            t = toup(ch);
            errno = 0;
            if (t == 'F') {
                ch = *p++;
                tok = TOK_CFLOAT;
                tokc.f = strtof(token_buf, NULL);
            } else if (t == 'L') {
                ch = *p++;
#ifdef TCC_TARGET_PE
                tok = TOK_CDOUBLE;
                tokc.d = strtod(token_buf, NULL);
#else
                tok = TOK_CLDOUBLE;
                tokc.ld = strtold(token_buf, NULL);
#endif
            } else {
                tok = TOK_CDOUBLE;
                tokc.d = strtod(token_buf, NULL);
            }
        }
    } else {
        unsigned long long n, n1;
        int lcount, ucount, ov = 0;
        const char *p1;

        /* integer number */
        *q = '\0';
        q = token_buf;
        if (b == 10 && *q == '0') {
            b = 8;
            q++;
        }
        n = 0;
        while(1) {
            t = *q++;
            /* no need for checks except for base 10 / 8 errors */
            if( t == '\0' )      break;
            else if( t >= 'a' )  t = t - 'a' + 10;
            else if( t >= 'A' )  t = t - 'A' + 10;
            else                 t = t - '0';
            if( t >= b )  tcc_error(-1, "invalid digit");
            n1 = n;
            n = n * b + t;
            /* detect overflow */
            if (n1 >= 0x1000000000000000ULL && n / b != n1)
                ov = 1;
        }

        /* Determine the characteristics (unsigned and/or 64bit) the type of
           the constant must have according to the constant suffix(es) */
        lcount = ucount = 0;
        p1 = p;
        for(;;) {
            t = toup(ch);
            if (t == 'L') {
                if( lcount >= 2 )  tcc_error(-1, "three 'l's in integer constant");
                if( lcount && *(p - 1) != ch )  tcc_error(-1, "incorrect integer suffix: %s", p1);
                lcount++;
                ch = *p++;
            } else if (t == 'U') {
                if( ucount >= 1 )  tcc_error(-1, "two 'u's in integer constant");
                ucount++;
                ch = *p++;
            } else {
                break;
            }
        }

        /* Determine if it needs 64 bits and/or unsigned in order to fit */
        if (ucount == 0 && b == 10) {
            if (lcount <= (LONG_SIZE == 4)) {
                if (n >= 0x80000000U)
                    lcount = (LONG_SIZE == 4) + 1;
            }
            if (n >= 0x8000000000000000ULL)
                ov = 1, ucount = 1;
        } else {
            if (lcount <= (LONG_SIZE == 4)) {
                if (n >= 0x100000000ULL)
                    lcount = (LONG_SIZE == 4) + 1;
                else if (n >= 0x80000000U)
                    ucount = 1;
            }
            if (n >= 0x8000000000000000ULL)
                ucount = 1;
        }

        if( ov )  tcc_error(0, "integer constant overflow");

        tok = TOK_CINT;
	if (lcount) {
            tok = TOK_CLONG;
            if (lcount == 2)
                tok = TOK_CLLONG;
	}
	if (ucount)
	    ++tok; /* TOK_CU... */
        tokc.i = n;
    }
    if( ch )  tcc_error(-1, "invalid number\n");
}


#define PARSE2(c1, tok1, c2, tok2)              \
    case c1:                                    \
        PEEKC(c, p);                            \
        if (c == c2) {                          \
            p++;                                \
            tok = tok2;                         \
        } else {                                \
            tok = tok1;                         \
        }                                       \
        break;

/* return next token without macro substitution */
static inline void next_nomacro1(void)
{
    int t, c, is_long, len;
    TokenSym *ts;
    uint8_t *p, *p1;
    unsigned int h;

    p = file->buf_ptr;
 redo_no_start:
    c = *p;
    switch(c) {
    case ' ':
    case '\t':
        tok = c;
        p++;
        if (parse_flags & PARSE_FLAG_SPACES)
            goto keep_tok_flags;
        while (isidnum_table[*p - CH_EOF] & IS_SPC)
            ++p;
        goto redo_no_start;
    case '\f':
    case '\v':
    case '\r':
        p++;
        goto redo_no_start;
    case '\\':
        /* first look if it is in fact an end of buffer */
        c = handle_stray1(p);
        p = file->buf_ptr;
        if (c == '\\')
            goto parse_simple;
        if (c != CH_EOF)
            goto redo_no_start;
        {
            TCCState *s1 = tcc_state;
            if ((parse_flags & PARSE_FLAG_LINEFEED)
                && !(tok_flags & TOK_FLAG_EOF)) {
                tok_flags |= TOK_FLAG_EOF;
                tok = TOK_LINEFEED;
                goto keep_tok_flags;
            } else if (!(parse_flags & PARSE_FLAG_PREPROCESS)) {
                tok = TOK_EOF;
            } else if (s1->ifdef_stack_ptr != file->ifdef_stack_ptr) {
                tcc_error(-1, "missing #endif");
            } else if (s1->include_stack_ptr == s1->include_stack) {
                /* no include left : end of file. */
                tok = TOK_EOF;
            } else {
                tok_flags &= ~TOK_FLAG_EOF;
                /* pop include file */
                
                /* test if previous '#endif' was after a #ifdef at
                   start of file */
                if (tok_flags & TOK_FLAG_ENDIF) {
#ifdef INC_DEBUG
                    printf("#endif %s\n", get_tok_str(file->ifndef_macro_saved, NULL));
#endif
                    search_cached_include(s1, file->filename, 1)
                        ->ifndef_macro = file->ifndef_macro_saved;
                    tok_flags &= ~TOK_FLAG_ENDIF;
                }

#if defined CONFIG_TCC_GDEBUG
                /* add end of include file debug info */
                if( tcc_state->do_debug )  put_stabd(N_EINCL, 0, 0);
#endif
                /* pop include stack */
                tcc_close();
                s1->include_stack_ptr--;
                p = file->buf_ptr;
                if (p == file->buffer)
                    tok_flags = TOK_FLAG_BOF|TOK_FLAG_BOL;
                goto redo_no_start;
            }
        }
        break;

    case '\n':
        file->line_num++;
        tok_flags |= TOK_FLAG_BOL;
        p++;
maybe_newline:
        if (0 == (parse_flags & PARSE_FLAG_LINEFEED))
            goto redo_no_start;
        tok = TOK_LINEFEED;
        goto keep_tok_flags;

    case '#':
        /* XXX: simplify */
        PEEKC(c, p);
        if ((tok_flags & TOK_FLAG_BOL) && 
            (parse_flags & PARSE_FLAG_PREPROCESS)) {
            file->buf_ptr = p;
            preprocess(tok_flags & TOK_FLAG_BOF);
            p = file->buf_ptr;
            goto maybe_newline;
        } else {
            if (c == '#') {
                p++;
                tok = TOK_TWOSHARPS;
            } else {
                if (parse_flags & PARSE_FLAG_ASM_FILE) {
                    p = parse_line_comment(p - 1);
                    goto redo_no_start;
                } else {
                    tok = '#';
                }
            }
        }
        break;
    
    /* dollar is allowed to start identifiers when not parsing asm */
    case '$':
        if (!(isidnum_table[c - CH_EOF] & IS_ID)
         || (parse_flags & PARSE_FLAG_ASM_FILE))
            goto parse_simple;

    case 'a': case 'b': case 'c': case 'd':
    case 'e': case 'f': case 'g': case 'h':
    case 'i': case 'j': case 'k': case 'l':
    case 'm': case 'n': case 'o': case 'p':
    case 'q': case 'r': case 's': case 't':
    case 'u': case 'v': case 'w': case 'x':
    case 'y': case 'z': 
    case 'A': case 'B': case 'C': case 'D':
    case 'E': case 'F': case 'G': case 'H':
    case 'I': case 'J': case 'K': 
    case 'M': case 'N': case 'O': case 'P':
    case 'Q': case 'R': case 'S': case 'T':
    case 'U': case 'V': case 'W': case 'X':
    case 'Y': case 'Z': 
    case '_':
    parse_ident_fast:
        p1 = p;
        h = TOK_HASH_INIT;
        h = TOK_HASH_FUNC(h, c);
        while (c = *++p, isidnum_table[c - CH_EOF] & (IS_ID|IS_NUM))
            h = TOK_HASH_FUNC(h, c);
        len = p - p1;
        if (c != '\\') {
            TokenSym **pts;

            /* fast case : no stray found, so we have the full token
               and we have already hashed it */
            h &= (TOK_HASH_SIZE - 1);
            pts = &hash_ident[h];
            for(;;) {
                ts = *pts;
                if (!ts)
                    break;
                if (ts->len == len && !memcmp(ts->str, p1, len))
                    goto token_found;
                pts = &(ts->hash_next);
            }
            ts = tok_alloc_new(pts, (char *) p1, len);
        token_found: ;
        } else {
            /* slower case */
            cstr_reset(&tokcstr);
            cstr_cat(&tokcstr, (char *) p1, len);
            p--;
            PEEKC(c, p);
        parse_ident_slow:
            while (isidnum_table[c - CH_EOF] & (IS_ID|IS_NUM))
            {
                cstr_ccat(&tokcstr, c);
                PEEKC(c, p);
            }
            ts = tok_alloc(tokcstr.data, tokcstr.size);
        }
        tok = ts->tok;
        break;
    case 'L':
        t = p[1];
        if (t != '\\' && t != '\'' && t != '\"') {
            /* fast case */
            goto parse_ident_fast;
        } else {
            PEEKC(c, p);
            if (c == '\'' || c == '\"') {
                is_long = 1;
                goto str_const;
            } else {
                cstr_reset(&tokcstr);
                cstr_ccat(&tokcstr, 'L');
                goto parse_ident_slow;
            }
        }
        break;

    case '0': case '1': case '2': case '3':
    case '4': case '5': case '6': case '7':
    case '8': case '9':
        t = c;
        PEEKC(c, p);
        /* after the first digit, accept digits, alpha, '.' or sign if
           prefixed by 'eEpP' */
    parse_num:
        cstr_reset(&tokcstr);
        for(;;) {
            cstr_ccat(&tokcstr, t);
            if (!((isidnum_table[c - CH_EOF] & (IS_ID|IS_NUM))
                  || c == '.'
                  || ((c == '+' || c == '-')
                      && (((t == 'e' || t == 'E')
                            && !(parse_flags & PARSE_FLAG_ASM_FILE
                                /* 0xe+1 is 3 tokens in asm */
                                && ((char*)tokcstr.data)[0] == '0'
                                && toup(((char*)tokcstr.data)[1]) == 'X'))
                          || t == 'p' || t == 'P'))))
                break;
            t = c;
            PEEKC(c, p);
        }
        /* We add a trailing '\0' to ease parsing */
        cstr_ccat(&tokcstr, '\0');
        tokc.str.size = tokcstr.size;
        tokc.str.data = tokcstr.data;
        tok = TOK_PPNUM;
        break;

    case '.':
        /* special dot handling because it can also start a number */
        PEEKC(c, p);
        if (isnum(c)) {
            t = '.';
            goto parse_num;
        } else if ((isidnum_table['.' - CH_EOF] & IS_ID)
                   && (isidnum_table[c - CH_EOF] & (IS_ID|IS_NUM))) {
            *--p = c = '.';
            goto parse_ident_fast;
        } else if (c == '.') {
            PEEKC(c, p);
            if (c == '.') {
                p++;
                tok = TOK_DOTS;
            } else {
                *--p = '.'; /* may underflow into file->unget[] */
                tok = '.';
            }
        } else {
            tok = '.';
        }
        break;
    case '\'':
    case '\"':
        is_long = 0;
    str_const:
        cstr_reset(&tokcstr);
        if (is_long)
            cstr_ccat(&tokcstr, 'L');
        cstr_ccat(&tokcstr, c);
        p = parse_pp_string(p, c, &tokcstr);
        cstr_ccat(&tokcstr, c);
        cstr_ccat(&tokcstr, '\0');
        tokc.str.size = tokcstr.size;
        tokc.str.data = tokcstr.data;
        tok = TOK_PPSTR;
        break;

    case '<':
        PEEKC(c, p);
        if (c == '=') {
            p++;
            tok = TOK_LE;
        } else if (c == '<') {
            PEEKC(c, p);
            if (c == '=') {
                p++;
                tok = TOK_A_SHL;
            } else {
                tok = TOK_SHL;
            }
        } else {
            tok = TOK_LT;
        }
        break;
    case '>':
        PEEKC(c, p);
        if (c == '=') {
            p++;
            tok = TOK_GE;
        } else if (c == '>') {
            PEEKC(c, p);
            if (c == '=') {
                p++;
                tok = TOK_A_SAR;
            } else {
                tok = TOK_SAR;
            }
        } else {
            tok = TOK_GT;
        }
        break;
        
    case '&':
        PEEKC(c, p);
        if (c == '&') {
            p++;
            tok = TOK_LAND;
        } else if (c == '=') {
            p++;
            tok = TOK_A_AND;
        } else {
            tok = '&';
        }
        break;
        
    case '|':
        PEEKC(c, p);
        if (c == '|') {
            p++;
            tok = TOK_LOR;
        } else if (c == '=') {
            p++;
            tok = TOK_A_OR;
        } else {
            tok = '|';
        }
        break;

    case '+':
        PEEKC(c, p);
        if (c == '+') {
            p++;
            tok = TOK_INC;
        } else if (c == '=') {
            p++;
            tok = TOK_A_ADD;
        } else {
            tok = '+';
        }
        break;
        
    case '-':
        PEEKC(c, p);
        if (c == '-') {
            p++;
            tok = TOK_DEC;
        } else if (c == '=') {
            p++;
            tok = TOK_A_SUB;
        } else if (c == '>') {
            p++;
            tok = TOK_ARROW;
        } else {
            tok = '-';
        }
        break;

    PARSE2('!', '!', '=', TOK_NE)
    PARSE2('=', '=', '=', TOK_EQ)
    PARSE2('*', '*', '=', TOK_A_MUL)
    PARSE2('%', '%', '=', TOK_A_MOD)
    PARSE2('^', '^', '=', TOK_A_XOR)
        
        /* comments or operator */
    case '/':
        PEEKC(c, p);
        if (c == '*') {
            p = parse_comment(p);
            /* comments replaced by a blank */
            tok = ' ';
            goto keep_tok_flags;
        } else if (c == '/') {
            p = parse_line_comment(p);
            tok = ' ';
            goto keep_tok_flags;
        } else if (c == '=') {
            p++;
            tok = TOK_A_DIV;
        } else {
            tok = '/';
        }
        break;
        
        /* simple tokens */
    case '(':
    case ')':
    case '[':
    case ']':
    case '{':
    case '}':
    case ',':
    case ';':
    case ':':
    case '?':
    case '~':
    case '@': /* only used in assembler */
    parse_simple:
        tok = c;
        p++;
        break;
    default:
        if (c >= 0x80 && c <= 0xFF) /* utf8 identifiers */
	    goto parse_ident_fast;
        if (parse_flags & PARSE_FLAG_ASM_FILE)
            goto parse_simple;
        tcc_error(-1, "unrecognized character \\x%02x", c);
        break;
    }
    tok_flags = 0;
keep_tok_flags:
    file->buf_ptr = p;
#if defined(PARSE_DEBUG)
    printf("token = %d %s\n", tok, get_tok_str(tok, &tokc));
#endif
}

/* return next token without macro substitution. Can read input from
   macro_ptr buffer */
static void next_nomacro_spc(void)
{
    if (macro_ptr) {
    redo:
        tok = *macro_ptr;
        if (tok) {
            TOK_GET(&tok, &macro_ptr, &tokc);
            if (tok == TOK_LINENUM) {
                file->line_num = tokc.i;
                goto redo;
            }
        }
    } else {
        next_nomacro1();
    }
    //printf("token = %s\n", get_tok_str(tok, &tokc));
}

ST_FUNC void next_nomacro(void)
{
    do {
        next_nomacro_spc();
    } while (tok < 256 && (isidnum_table[tok - CH_EOF] & IS_SPC));
}
 

static void macro_subst(
    TokenString *tok_str,
    Sym **nested_list,
    const int *macro_str
    );

/* substitute arguments in replacement lists in macro_str by the values in
   args (field d) and return allocated string */
static int *macro_arg_subst(Sym **nested_list, const int *macro_str, Sym *args)
{
    int t, t0, t1, spc;
    const int *st;
    Sym *s;
    CValue cval;
    TokenString str;
    CString cstr;

    tok_str_new(&str);
    t0 = t1 = 0;
    while(1) {
        TOK_GET(&t, &macro_str, &cval);
        if (!t)
            break;
        if (t == '#') {
            /* stringize */
            TOK_GET(&t, &macro_str, &cval);
            if (!t)
                goto bad_stringy;
            s = sym_find2(args, t);
            if (s) {
                cstr_new(&cstr);
                cstr_ccat(&cstr, '\"');
                st = s->d;
                spc = 0;
                while (*st >= 0) {
                    TOK_GET(&t, &st, &cval);
                    if (t != TOK_PLCHLDR
                     && t != TOK_NOSUBST
                     && 0 == check_space(t, &spc)) {
                        const char *s = get_tok_str(t, &cval);
                        while (*s) {
                            if (t == TOK_PPSTR && *s != '\'')
                                add_char(&cstr, *s);
                            else
                                cstr_ccat(&cstr, *s);
                            ++s;
                        }
                    }
                }
                cstr.size -= spc;
                cstr_ccat(&cstr, '\"');
                cstr_ccat(&cstr, '\0');
#ifdef PP_DEBUG
                printf("\nstringize: <%s>\n", (char *)cstr.data);
#endif
                /* add string */
                cval.str.size = cstr.size;
                cval.str.data = cstr.data;
                tok_str_add2(&str, TOK_PPSTR, &cval);
                cstr_free(&cstr);
            } else {
        bad_stringy:
                tcc_error(-1, "macro parameter after '#' expected" );
            }
        } else if (t >= TOK_IDENT) {
            s = sym_find2(args, t);
            if (s) {
                int l0 = str.len;
                st = s->d;
                /* if '##' is present before or after, no arg substitution */
                if (*macro_str == TOK_PPJOIN || t1 == TOK_PPJOIN) {
                    /* special case for var arg macros : ## eats the ','
                       if empty VA_ARGS variable. */
                    if (t1 == TOK_PPJOIN && t0 == ',' && gnu_ext && s->type.t) {
                        if (*st <= 0) {
                            /* suppress ',' '##' */
                            str.len -= 2;
                        } else {
                            /* suppress '##' and add variable */
                            str.len--;
                            goto add_var;
                        }
                    }
                } else {
            add_var:
		    if (!s->next) {
			/* Expand arguments tokens and store them.  In most
			   cases we could also re-expand each argument if
			   used multiple times, but not if the argument
			   contains the __COUNTER__ macro.  */
			TokenString str2;
			sym_push2(&s->next, s->v, s->type.t, 0);
			tok_str_new(&str2);
			macro_subst(&str2, nested_list, st);
			tok_str_add(&str2, 0);
			s->next->d = str2.str;
		    }
		    st = s->next->d;
                }
                for(;;) {
                    int t2;
                    TOK_GET(&t2, &st, &cval);
                    if (t2 <= 0)
                        break;
                    tok_str_add2(&str, t2, &cval);
                }
                if (str.len == l0) /* expanded to empty string */
                    tok_str_add(&str, TOK_PLCHLDR);
            } else {
                tok_str_add(&str, t);
            }
        } else {
            tok_str_add2(&str, t, &cval);
        }
        t0 = t1, t1 = t;
    }
    tok_str_add(&str, 0);
    return str.str;
}

static char const ab_month_name[12][4] =
{
    "Jan", "Feb", "Mar", "Apr", "May", "Jun",
    "Jul", "Aug", "Sep", "Oct", "Nov", "Dec"
};

static int paste_tokens(int t1, CValue *v1, int t2, CValue *v2)
{
    CString cstr;
    int n, ret = 1;

    cstr_new(&cstr);
    if (t1 != TOK_PLCHLDR)
        cstr_cat(&cstr, get_tok_str(t1, v1), -1);
    n = cstr.size;
    if (t2 != TOK_PLCHLDR)
        cstr_cat(&cstr, get_tok_str(t2, v2), -1);
    cstr_ccat(&cstr, '\0');

    tcc_open_bf(tcc_state, ":paste:", cstr.size);
    memcpy(file->buffer, cstr.data, cstr.size);
    tok_flags = 0;
    for (;;) {
        next_nomacro1();
        if (0 == *file->buf_ptr)
            break;
        if (is_space(tok))
            continue;
        tcc_error(0, "pasting \"%.*s\" and \"%s\" does not give a valid preprocessing token", n, cstr.data, (char*)cstr.data + n);
        ret = 0;
        break;
    }
    tcc_close();
    //printf("paste <%s>\n", (char*)cstr.data);
    cstr_free(&cstr);
    return ret;
}

/* handle the '##' operator. Return NULL if no '##' seen. Otherwise
   return the resulting string (which must be freed). */
static inline int *macro_twosharps(const int *ptr0)
{
    int t;
    CValue cval;
    TokenString macro_str1;
    int start_of_nosubsts = -1;
    const int *ptr;

    /* we search the first '##' */
    for (ptr = ptr0;;) {
        TOK_GET(&t, &ptr, &cval);
        if (t == TOK_PPJOIN)
            break;
        if (t == 0)
            return NULL;
    }

    tok_str_new(&macro_str1);

    for (ptr = ptr0;;) {
        TOK_GET(&t, &ptr, &cval);
        if (t == 0)
            break;
        if (t == TOK_PPJOIN)
            continue;
        while (*ptr == TOK_PPJOIN) {
            int t1; CValue cv1;
            /* given 'a##b', remove nosubsts preceding 'a' */
            if (start_of_nosubsts >= 0)
                macro_str1.len = start_of_nosubsts;
            /* given 'a##b', remove nosubsts preceding 'b' */
            while ((t1 = *++ptr) == TOK_NOSUBST)
                ;
            if (t1 && t1 != TOK_PPJOIN) {
                TOK_GET(&t1, &ptr, &cv1);
                if (t != TOK_PLCHLDR || t1 != TOK_PLCHLDR) {
                    if (paste_tokens(t, &cval, t1, &cv1)) {
                        t = tok, cval = tokc;
                    } else {
                        tok_str_add2(&macro_str1, t, &cval);
                        t = t1, cval = cv1;
                    }
                }
            }
        }
        if (t == TOK_NOSUBST) {
            if (start_of_nosubsts < 0)
                start_of_nosubsts = macro_str1.len;
        } else {
            start_of_nosubsts = -1;
        }
        tok_str_add2(&macro_str1, t, &cval);
    }
    tok_str_add(&macro_str1, 0);
    return macro_str1.str;
}

/* peek or read [ws_str == NULL] next token from function macro call,
   walking up macro levels up to the file if necessary */
static int next_argstream(Sym **nested_list, TokenString *ws_str)
{
    int t;
    const int *p;
    Sym *sa;

    for (;;) {
        if (macro_ptr) {
            p = macro_ptr, t = *p;
            if (ws_str) {
                while (is_space(t) || TOK_LINEFEED == t || TOK_PLCHLDR == t)
                    tok_str_add(ws_str, t), t = *++p;
            }
            if (t == 0) {
                end_macro();
                /* also, end of scope for nested defined symbol */
                sa = *nested_list;
                while (sa && sa->v == 0)
                    sa = sa->prev;
                if (sa)
                    sa->v = 0;
                continue;
            }
        } else {
            ch = handle_eob();
            if (ws_str) {
                while (is_space(ch) || ch == '\n' || ch == '/') {
                    if (ch == '/') {
                        int c;
                        uint8_t *p = file->buf_ptr;
                        PEEKC(c, p);
                        if (c == '*') {
                            p = parse_comment(p);
                            file->buf_ptr = p - 1;
                        } else if (c == '/') {
                            p = parse_line_comment(p);
                            file->buf_ptr = p - 1;
                        } else
                            break;
                        ch = ' ';
                    }
                    if (ch == '\n')
                        file->line_num++;
                    if (!(ch == '\f' || ch == '\v' || ch == '\r'))
                        tok_str_add(ws_str, ch);
                    cinp();
                }
            }
            t = ch;
        }

        if (ws_str)
            return t;
        next_nomacro_spc();
        return tok;
    }
}

/* do macro substitution of current token with macro 's' and add
   result to (tok_str,tok_len). 'nested_list' is the list of all
   macros we got inside to avoid recursing. Return non zero if no
   substitution needs to be done */
static int macro_subst_tok(
    TokenString *tok_str,
    Sym **nested_list,
    Sym *s)
{
    Sym *args, *sa, *sa1;
    int parlevel, t, t1, spc;
    TokenString str;
    char *cstrval;
    CValue cval;
    CString cstr;
    char buf[32];

    /* if symbol is a macro, prepare substitution */
    /* special macros */
    if (tok == TOK___LINE__ || tok == TOK___COUNTER__) {
        t = tok == TOK___LINE__ ? file->line_num : pp_counter++;
        snprintf(buf, sizeof(buf), "%d", t);
        cstrval = buf;
        t1 = TOK_PPNUM;
        goto add_cstr1;
    } else if (tok == TOK___FILE__) {
        cstrval = file->filename;
        goto add_cstr;
    } else if (tok == TOK___DATE__ || tok == TOK___TIME__) {
        time_t ti;
        struct tm *tm;

        time(&ti);
        tm = localtime(&ti);
        if (tok == TOK___DATE__) {
            snprintf(buf, sizeof(buf), "%s %2d %d", 
                     ab_month_name[tm->tm_mon], tm->tm_mday, tm->tm_year + 1900);
        } else {
            snprintf(buf, sizeof(buf), "%02d:%02d:%02d", 
                     tm->tm_hour, tm->tm_min, tm->tm_sec);
        }
        cstrval = buf;
    add_cstr:
        t1 = TOK_STR;
    add_cstr1:
        cstr_new(&cstr);
        cstr_cat(&cstr, cstrval, 0);
        cval.str.size = cstr.size;
        cval.str.data = cstr.data;
        tok_str_add2(tok_str, t1, &cval);
        cstr_free(&cstr);
    } else if (s->d) {
        int saved_parse_flags = parse_flags;
	int *joined_str = NULL;
        int *mstr = s->d;

        if (s->type.t == MACRO_FUNC) {
            /* whitespace between macro name and argument list */
            TokenString ws_str;
            tok_str_new(&ws_str);

            spc = 0;
            parse_flags |= PARSE_FLAG_SPACES | PARSE_FLAG_LINEFEED
                | PARSE_FLAG_ACCEPT_STRAYS;

            /* get next token from argument stream */
            t = next_argstream(nested_list, &ws_str);
            if (t != '(') {
                /* not a macro substitution after all, restore the
                 * macro token plus all whitespace we've read.
                 * whitespace is intentionally not merged to preserve
                 * newlines. */
                parse_flags = saved_parse_flags;
                tok_str_add(tok_str, tok);
                if (parse_flags & PARSE_FLAG_SPACES) {
                    int i;
                    for (i = 0; i < ws_str.len; i++)
                        tok_str_add(tok_str, ws_str.str[i]);
                }
                tok_str_free_str(ws_str.str);
                return 0;
            } else {
                tok_str_free_str(ws_str.str);
            }
	    do {
		next_nomacro(); /* eat '(' */
	    } while (tok == TOK_PLCHLDR);

            /* argument macro */
            args = NULL;
            sa = s->next;
            /* NOTE: empty args are allowed, except if no args */
            for(;;) {
                do {
                    next_argstream(nested_list, NULL);
                } while (is_space(tok) || TOK_LINEFEED == tok);
    empty_arg:
                /* handle '()' case */
                if (!args && !sa && tok == ')')
                    break;
                if( !sa )  tcc_error(-1, "macro '%s' used with too many args", get_tok_str(s->v, 0));
                tok_str_new(&str);
                parlevel = spc = 0;
                /* NOTE: non zero sa->t indicates VA_ARGS */
                while ((parlevel > 0 || 
                        (tok != ')' && 
                         (tok != ',' || sa->type.t)))) {
                    if (tok == TOK_EOF || tok == 0)
                        break;
                    if (tok == '(')
                        parlevel++;
                    else if (tok == ')')
                        parlevel--;
                    if (tok == TOK_LINEFEED)
                        tok = ' ';
                    if (!check_space(tok, &spc))
                        tok_str_add2(&str, tok, &tokc);
                    next_argstream(nested_list, NULL);
                }
                if( parlevel )  tcc_error(-1, ") expected" );
                str.len -= spc;
                tok_str_add(&str, -1);
                tok_str_add(&str, 0);
                sa1 = sym_push2(&args, sa->v & ~SYM_FIELD, sa->type.t, 0);
                sa1->d = str.str;
                sa = sa->next;
                if (tok == ')') {
                    /* special case for gcc var args: add an empty
                       var arg argument if it is omitted */
                    if (sa && sa->type.t && gnu_ext)
                        goto empty_arg;
                    break;
                }
                if( tok != ',' )  tcc_error(-1, ", expected" );
            }
            if (sa) {
                tcc_error(-1, "macro '%s' used with too few args",
                      get_tok_str(s->v, 0));
            }

            parse_flags = saved_parse_flags;

            /* now subst each arg */
            mstr = macro_arg_subst(nested_list, mstr, args);
            /* free memory */
            sa = args;
            while (sa) {
                sa1 = sa->prev;
                tok_str_free_str(sa->d);
                if (sa->next) {
                    tok_str_free_str(sa->next->d);
                    sym_free(sa->next);
                }
                sym_free(sa);
                sa = sa1;
            }
        }

        sym_push2(nested_list, s->v, 0, 0);
        parse_flags = saved_parse_flags;
        joined_str = macro_twosharps(mstr);
        macro_subst(tok_str, nested_list, joined_str ? joined_str : mstr);

        /* pop nested defined symbol */
        sa1 = *nested_list;
        *nested_list = sa1->prev;
        sym_free(sa1);
	if (joined_str)
	    tok_str_free_str(joined_str);
        if (mstr != s->d)
            tok_str_free_str(mstr);
    }
    return 0;
}

/* do macro substitution of macro_str and add result to
   (tok_str,tok_len). 'nested_list' is the list of all macros we got
   inside to avoid recursing. */
static void macro_subst(
    TokenString *tok_str,
    Sym **nested_list,
    const int *macro_str
    )
{
    Sym *s;
    int t, spc, nosubst;
    CValue cval;
    
    spc = nosubst = 0;

    while (1) {
        TOK_GET(&t, &macro_str, &cval);
        if (t <= 0)
            break;

        if (t >= TOK_IDENT && 0 == nosubst) {
            s = define_find(t);
            if (s == NULL)
                goto no_subst;

            /* if nested substitution, do nothing */
            if (sym_find2(*nested_list, t)) {
                /* and mark it as TOK_NOSUBST, so it doesn't get subst'd again */
                tok_str_add2(tok_str, TOK_NOSUBST, NULL);
                goto no_subst;
            }

            {
                TokenString str;
                str.str = (int*)macro_str;
                begin_macro(&str, 2);

                tok = t;
                macro_subst_tok(tok_str, nested_list, s);

                if (str.alloc == 3) {
                    /* already finished by reading function macro arguments */
                    break;
                }

                macro_str = macro_ptr;
                end_macro ();
            }
            if (tok_str->len)
                spc = is_space(t = tok_str->str[tok_str->lastlen]);
        } else {
            if (t == '\\' && !(parse_flags & PARSE_FLAG_ACCEPT_STRAYS))
                tcc_error(-1, "stray '\\' in program");
no_subst:
            if (!check_space(t, &spc))
                tok_str_add2(tok_str, t, &cval);

            if (nosubst) {
                if (nosubst > 1 && (spc || (++nosubst == 3 && t == '(')))
                    continue;
                nosubst = 0;
            }
            if (t == TOK_NOSUBST)
                nosubst = 1;
        }
        /* GCC supports 'defined' as result of a macro substitution */
        if (t == TOK_DEFINED && pp_expr)
            nosubst = 2;
    }
}

/* return next token with macro substitution */
ST_FUNC void next(void)
{
 redo:
    if (parse_flags & PARSE_FLAG_SPACES)
        next_nomacro_spc();
    else
        next_nomacro();

    if (macro_ptr) {
        if (tok == TOK_NOSUBST || tok == TOK_PLCHLDR) {
        /* discard preprocessor markers */
            goto redo;
        } else if (tok == 0) {
            /* end of macro or unget token string */
            end_macro();
            goto redo;
        }
    } else if (tok >= TOK_IDENT && (parse_flags & PARSE_FLAG_PREPROCESS)) {
        Sym *s;
        /* if reading from file, try to substitute macros */
        s = define_find(tok);
        if (s) {
            Sym *nested_list = NULL;
            tokstr_buf.len = 0;
            macro_subst_tok(&tokstr_buf, &nested_list, s);
            tok_str_add(&tokstr_buf, 0);
            begin_macro(&tokstr_buf, 2);
            goto redo;
        }
    }
    /* convert preprocessor tokens into C tokens */
    if (tok == TOK_PPNUM) {
        if  (parse_flags & PARSE_FLAG_TOK_NUM)
            parse_number((char *)tokc.str.data);
    } else if (tok == TOK_PPSTR) {
        if (parse_flags & PARSE_FLAG_TOK_STR)
            parse_string((char *)tokc.str.data, tokc.str.size - 1);
    }
}

/* push back current token and set current token to 'last_tok'. Only
   identifier case handled for labels. */
ST_INLN void unget_tok(int last_tok)
{

    TokenString *str = tok_str_alloc();
    tok_str_add2(str, tok, &tokc);
    tok_str_add(str, 0);
    begin_macro(str, 1);
    tok = last_tok;
}

ST_FUNC void preprocess_start(TCCState *s1, int is_asm)
{
    CString cstr;
    int i;

    s1->include_stack_ptr = s1->include_stack;
    s1->ifdef_stack_ptr = s1->ifdef_stack;
    file->ifdef_stack_ptr = s1->ifdef_stack_ptr;
    pp_expr = 0;
    pp_counter = 0;
    pp_debug_tok = pp_debug_symv = 0;
    pp_once++;
    pvtop = vtop = vstack - 1;
    s1->pack_stack[0] = 0;
    s1->pack_stack_ptr = s1->pack_stack;

    set_idnum('$', s1->dollars_in_identifiers ? IS_ID : 0);
    set_idnum('.', is_asm ? IS_ID : 0);

    cstr_new(&cstr);
    cstr_cat(&cstr, "\"", -1);
    cstr_cat(&cstr, file->filename, -1);
    cstr_cat(&cstr, "\"", 0);
    tcc_define_symbol(s1, "__BASE_FILE__", cstr.data);

    cstr_reset(&cstr);
    for (i = 0; i < s1->nb_cmd_include_files; i++) {
        cstr_cat(&cstr, "#include \"", -1);
        cstr_cat(&cstr, s1->cmd_include_files[i], -1);
        cstr_cat(&cstr, "\"\n", -1);
    }
    if (cstr.size) {
        *s1->include_stack_ptr++ = file;
	tcc_open_bf(s1, "<command line>", cstr.size);
	memcpy(file->buffer, cstr.data, cstr.size);
    }
    cstr_free(&cstr);

    if (is_asm)
        tcc_define_symbol(s1, "__ASSEMBLER__", NULL);

    parse_flags = is_asm ? PARSE_FLAG_ASM_FILE : 0;
    tok_flags = TOK_FLAG_BOL | TOK_FLAG_BOF;
}

/* cleanup from error/setjmp */
ST_FUNC void preprocess_end(TCCState *s1)
{
    while( macro_stack ) end_macro();
    macro_ptr = NULL;
}

ST_FUNC void tccpp_new(TCCState *s)
{
    int i, c;
    const char *p, *r;

    /* might be used in error() before preprocess_start() */
    s->include_stack_ptr = s->include_stack;

    /* init isid table */
    for(i = CH_EOF; i<128; i++)
        set_idnum(i,
            is_space(i) ? IS_SPC
            : isid(i) ? IS_ID
            : isnum(i) ? IS_NUM
            : 0);

    for(i = 128; i<256; i++)
        set_idnum(i, IS_ID);

    /* init allocators */
    tal_new(&toksym_alloc, TOKSYM_TAL_LIMIT, TOKSYM_TAL_SIZE);
    tal_new(&tokstr_alloc, TOKSTR_TAL_LIMIT, TOKSTR_TAL_SIZE);
    tal_new(&cstr_alloc, CSTR_TAL_LIMIT, CSTR_TAL_SIZE);

    memset(hash_ident, 0, TOK_HASH_SIZE * sizeof(TokenSym *));
    cstr_new(&cstr_buf);
    cstr_realloc(&cstr_buf, STRING_MAX_SIZE);
    tok_str_new(&tokstr_buf);
    tok_str_realloc(&tokstr_buf, TOKSTR_MAX_SIZE);
    
    tok_ident = TOK_IDENT;
    p = tcc_keywords;
    while (*p) {
        r = p;
        for(;;) {
            c = *r++;
            if (c == '\0')
                break;
        }
        tok_alloc(p, r - p - 1);
        p = r;
    }
}

ST_FUNC void tccpp_delete(TCCState *s)
{
    int i, n;

    /* free -D and compiler defines */
    free_defines(NULL);

    /* free tokens */
    n = tok_ident - TOK_IDENT;
    for(i = 0; i < n; i++)
        tal_free(toksym_alloc, table_ident[i]);
    tcc_free(table_ident);
    table_ident = NULL;

    /* free static buffers */
    cstr_free(&tokcstr);
    cstr_free(&cstr_buf);
    cstr_free(&macro_equal_buf);
    tok_str_free_str(tokstr_buf.str);

    /* free allocators */
    tal_delete(toksym_alloc);
    toksym_alloc = NULL;
    tal_delete(tokstr_alloc);
    tokstr_alloc = NULL;
    tal_delete(cstr_alloc);
    cstr_alloc = NULL;
}

/* ------------------------------------------------------------------------- */

/*  TCC - Tiny C Compiler
 *  Copyright (c) 2001-2004 Fabrice Bellard
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */

/********************************************************/
/* global variables */

/* loc : local variable index
   ind : output code index
   rsym: return symbol
   anon_sym: anonymous symbol index
*/
ST_DATA int rsym, anon_sym, ind, loc;

ST_DATA Sym *sym_free_first;
ST_DATA void **sym_pools;
ST_DATA int nb_sym_pools;

ST_DATA Sym *global_stack;
ST_DATA Sym *local_stack;
ST_DATA Sym *define_stack;
ST_DATA Sym *global_label_stack;
ST_DATA Sym *local_label_stack;
static int local_scope;
static int in_sizeof;
static int section_sym;

ST_DATA int vlas_in_scope; /* number of VLAs that are currently in scope */
ST_DATA int vla_sp_root_loc; /* vla_sp_loc for SP before any VLAs were pushed */
ST_DATA int vla_sp_loc; /* Pointer to variable holding location to store stack pointer on the stack when modifying stack pointer */

ST_DATA SValue __vstack[1+VSTACK_SIZE], *vtop, *pvtop;

ST_DATA int const_wanted; /* true if constant wanted */
ST_DATA int nocode_wanted; /* no code generation wanted */
#define NODATA_WANTED (nocode_wanted > 0) /* no static data output wanted either */
#define STATIC_DATA_WANTED (nocode_wanted & 0xC0000000) /* only static data output */
ST_DATA int global_expr;  /* true if compound literals must be allocated globally (used during initializers parsing */
ST_DATA CType func_vt; /* current function return type (used by return instruction) */
ST_DATA int func_var; /* true if current function is variadic (used by return instruction) */
ST_DATA int func_vc;
ST_DATA int last_line_num, last_ind, func_ind; /* debug last line number and pc */
ST_DATA const char *funcname;

ST_DATA CType char_pointer_type, func_old_type, int_type, size_type, ptrdiff_type;

ST_DATA struct switch_t {
    struct case_t {
        int64_t v1, v2;
	int sym;
    } **p; int n; /* list of case ranges */
    int def_sym; /* default symbol */
} *cur_switch; /* current switch */

/* ------------------------------------------------------------------------- */

static void gen_cast(CType *type);
static void gen_cast_s(int t);
static inline CType *pointed_type(CType *type);
static int is_compatible_types(CType *type1, CType *type2);
static int parse_btype(CType *type, AttributeDef *ad);
static CType *type_decl(CType *type, AttributeDef *ad, int *v, int td);
static void parse_expr_type(CType *type);
static void init_putv(CType *type, Section *sec, unsigned long c);
static void decl_initializer(CType *type, Section *sec, unsigned long c, int first, int size_only);
static void block(int *bsym, int *csym, int is_expr);
static void decl_initializer_alloc(CType *type, AttributeDef *ad, int r, int has_init, int v, int scope);
static void decl(int l);
static int decl0(int l, int is_for_loop_init, Sym *);
static void expr_eq(void);
static void vla_runtime_type_size(CType *type, int *a);
static void vla_sp_restore(void);
static void vla_sp_restore_root(void);
static int is_compatible_unqualified_types(CType *type1, CType *type2);
static inline int64_t expr_const64(void);
static void vpush64(int ty, unsigned long long v);
static void vpush(CType *type);
static int gvtst(int inv, int t);
static void gen_inline_functions(TCCState *s);
static void skip_or_save_block(TokenString **str);
static void gv_dup(void);

ST_INLN int is_float(int t)
{
    int bt;
    bt = t & VT_BTYPE;
    return bt == VT_LDOUBLE || bt == VT_DOUBLE || bt == VT_FLOAT || bt == VT_QFLOAT;
}

/* we use our own 'finite' function to avoid potential problems with
   non standard math libs */
/* XXX: endianness dependent */
ST_FUNC int ieee_finite(double d)
{
    int p[4];
    memcpy(p, &d, sizeof(double));
    return ((unsigned)((p[1] | 0x800fffff) + 1)) >> 31;
}

/* compiling intel long double natively */
#if (defined __i386__ || defined __x86_64__) \
    && (defined TCC_TARGET_I386 || defined TCC_TARGET_X86_64)
# define TCC_IS_NATIVE_387
#endif

ST_FUNC void test_lvalue(void)
{
    if( !( vtop->r & VT_LVAL ))  tcc_error(-1, "lvalue expected" );
}

ST_FUNC void check_vstack(void)
{
    if( pvtop != vtop )  tcc_error(-1, "internal compiler error: vstack leak (%d)", vtop - pvtop);
}

/* ------------------------------------------------------------------------- */

#if defined CONFIG_TCC_GDEBUG

/* start of translation unit info */
ST_FUNC void tcc_debug_start(TCCState *s1) {
    if( s1->do_debug ) {
        char buf[512];
        /* file info: full path + filename */
        section_sym = put_elf_sym(symtab_section, 0, 0, ELFW(ST_INFO)(STB_LOCAL, STT_SECTION), 0,
                                  text_section->sh_num, NULL);
        getcwd(buf, sizeof(buf));
        pstrcat(buf, sizeof(buf), "/");
        put_stabs_r(buf,            N_SO, 0, 0, text_section->data_offset, text_section, section_sym);
        put_stabs_r(file->filename, N_SO, 0, 0, text_section->data_offset, text_section, section_sym);
        last_ind = 0;
        last_line_num = 0;
    }
}

/* put end of translation unit info */
ST_FUNC void tcc_debug_end(TCCState *s1) {
    if( s1->do_debug ) put_stabs_r(NULL, N_SO, 0, 0, text_section->data_offset, text_section, section_sym);
}

/* generate line number info */
ST_FUNC void tcc_debug_line(TCCState *s1) {
    if( s1->do_debug && ( last_line_num != file->line_num || last_ind != ind )) {
        put_stabn(N_SLINE, 0, file->line_num, ind - func_ind);
        last_ind = ind;
        last_line_num = file->line_num;
    }
}

/* put function symbol */
ST_FUNC void tcc_debug_funcstart(TCCState *s1, Sym *sym) {
    char buf[512];
    if( s1->do_debug ) {
        /* stabs info */
        /* XXX: we put here a dummy type */
        snprintf(buf, sizeof(buf), "%s:%c1", funcname, sym->type.t & VT_STATIC ? 'f' : 'F');
        put_stabs_r(buf, N_FUN, 0, file->line_num, 0, cur_text_section, sym->c);
        /* //gr gdb wants a line at the function */
        put_stabn(N_SLINE, 0, file->line_num, 0);
        last_ind = 0;
        last_line_num = 0;
    }
}

/* put function size */
ST_FUNC void tcc_debug_funcend(TCCState *s1, int size) {
    if( s1->do_debug ) put_stabn(N_FUN, 0, 0, size);
}

#endif  /**  #if defined CONFIG_TCC_GDEBUG  **/


/* ------------------------------------------------------------------------- */
ST_FUNC int tccgen_compile(TCCState *s1) {
    cur_text_section = NULL;
    funcname = "";
    anon_sym = SYM_FIRST_ANOM;
    section_sym = 0;
    const_wanted = 0;
    nocode_wanted = 0x80000000;
    /* define some often used types */
    int_type.t = VT_INT;
    char_pointer_type.t = VT_BYTE;
    mk_pointer(&char_pointer_type);
#if PTR_SIZE == 4
    size_type.t = VT_INT | VT_UNSIGNED;
    ptrdiff_type.t = VT_INT;
#elif LONG_SIZE == 4
    size_type.t = VT_LLONG | VT_UNSIGNED;
    ptrdiff_type.t = VT_LLONG;
#else
    size_type.t = VT_LONG | VT_LLONG | VT_UNSIGNED;
    ptrdiff_type.t = VT_LONG | VT_LLONG;
#endif
    func_old_type.t = VT_FUNC;
    func_old_type.ref = sym_push(SYM_FIELD, &int_type, 0, 0);
    func_old_type.ref->f.func_call = FUNC_CDECL;
    func_old_type.ref->f.func_type = FUNC_OLD;
#if defined CONFIG_TCC_GDEBUG
    tcc_debug_start(s1);
#endif
    /* an elf symbol of type STT_FILE must be put so that STB_LOCAL symbols can be safely used */
    put_elf_sym( symtab_section, 0, 0, ELFW(ST_INFO)(STB_LOCAL, STT_FILE), 0, SHN_ABS, file->filename );
#ifdef TCC_TARGET_ARM
    arm_init(s1);
#endif
#ifdef INC_DEBUG
    printf("%s: **** new file\n", file->filename);
#endif
    parse_flags = PARSE_FLAG_PREPROCESS | PARSE_FLAG_TOK_NUM | PARSE_FLAG_TOK_STR;
    next();
    decl(VT_CONST);
    gen_inline_functions(s1);
    check_vstack();
#if defined CONFIG_TCC_GDEBUG
    tcc_debug_end(s1);  // end of translation unit info
#endif
    return 0;
}

/* ------------------------------------------------------------------------- */
ST_FUNC ElfSym *elfsym(Sym *s)
{
  if (!s || !s->c)
    return NULL;
  return &((ElfSym *)symtab_section->data)[s->c];
}

/* apply storage attributes to Elf symbol */
ST_FUNC void update_storage(Sym *sym)
{
    ElfSym *esym;
    int sym_bind, old_sym_bind;

    esym = elfsym(sym);
    if (!esym)
        return;

    if (sym->a.visibility)
        esym->st_other = (esym->st_other & ~ELFW(ST_VISIBILITY)(-1))
            | sym->a.visibility;

    if (sym->type.t & VT_STATIC)
        sym_bind = STB_LOCAL;
    else if (sym->a.weak)
        sym_bind = STB_WEAK;
    else
        sym_bind = STB_GLOBAL;
    old_sym_bind = ELFW(ST_BIND)(esym->st_info);
    if (sym_bind != old_sym_bind) {
        esym->st_info = ELFW(ST_INFO)(sym_bind, ELFW(ST_TYPE)(esym->st_info));
    }

#ifdef TCC_TARGET_PE
    if (sym->a.dllimport)
        esym->st_other |= ST_PE_IMPORT;
    if (sym->a.dllexport)
        esym->st_other |= ST_PE_EXPORT;
#endif

#if 0
    printf("storage %s: bind=%c vis=%d exp=%d imp=%d\n",
        get_tok_str(sym->v, NULL),
        sym_bind == STB_WEAK ? 'w' : sym_bind == STB_LOCAL ? 'l' : 'g',
        sym->a.visibility,
        sym->a.dllexport,
        sym->a.dllimport
        );
#endif
}

/* ------------------------------------------------------------------------- */
/* update sym->c so that it points to an external symbol in section
   'section' with value 'value' */

ST_FUNC void put_extern_sym2(Sym *sym, int sh_num,
                            addr_t value, unsigned long size,
                            int can_add_underscore)
{
    int sym_type, sym_bind, info, other, t;
    ElfSym *esym;
    const char *name;
    char buf1[256];
#ifdef CONFIG_TCC_BCHECK
    char buf[32];
#endif

    if (!sym->c) {
        name = get_tok_str(sym->v, NULL);
#ifdef CONFIG_TCC_BCHECK
        if( tcc_state->do_bounds_check ) {
            /* XXX: avoid doing that for statics ? */
            /* if bound checking is activated, we change some function
               names by adding the "__bound" prefix */
            switch(sym->v) {
            case TOK_memcpy:
            case TOK_memmove:
            case TOK_memset:
            case TOK_strlen:
            case TOK_strcpy:
            case TOK_alloca:
                strcpy(buf, "__bound_");
                strcat(buf, name);
                name = buf;
                break;
            }
        }
#endif
        t = sym->type.t;
        if ((t & VT_BTYPE) == VT_FUNC) {
            sym_type = STT_FUNC;
        } else if ((t & VT_BTYPE) == VT_VOID) {
            sym_type = STT_NOTYPE;
        } else {
            sym_type = STT_OBJECT;
        }
        if (t & VT_STATIC)
            sym_bind = STB_LOCAL;
        else
            sym_bind = STB_GLOBAL;
        other = 0;
#ifdef TCC_TARGET_PE
        if (sym_type == STT_FUNC && sym->type.ref) {
            Sym *ref = sym->type.ref;
            if (ref->f.func_call == FUNC_STDCALL && can_add_underscore) {
                sprintf(buf1, "_%s@%d", name, ref->f.func_args * PTR_SIZE);
                name = buf1;
                other |= ST_PE_STDCALL;
                can_add_underscore = 0;
            }
        }
#endif
        if (tcc_state->leading_underscore && can_add_underscore) {
            buf1[0] = '_';
            pstrcpy(buf1 + 1, sizeof(buf1) - 1, name);
            name = buf1;
        }
        if (sym->asm_label)
            name = get_tok_str(sym->asm_label, NULL);
        info = ELFW(ST_INFO)(sym_bind, sym_type);
        sym->c = put_elf_sym(symtab_section, value, size, info, other, sh_num, name);
    } else {
        esym = elfsym(sym);
        esym->st_value = value;
        esym->st_size = size;
        esym->st_shndx = sh_num;
    }
    update_storage(sym);
}

ST_FUNC void put_extern_sym(Sym *sym, Section *section,
                           addr_t value, unsigned long size)
{
    int sh_num = section ? section->sh_num : SHN_UNDEF;
    put_extern_sym2(sym, sh_num, value, size, 1);
}

/* add a new relocation entry to symbol 'sym' in section 's' */
ST_FUNC void greloca(Section *s, Sym *sym, unsigned long offset, int type,
                     addr_t addend)
{
    int c = 0;

    if (nocode_wanted && s == cur_text_section)
        return;

    if (sym) {
        if (0 == sym->c)
            put_extern_sym(sym, NULL, 0, 0);
        c = sym->c;
    }

    /* now we can add ELF relocation info */
    put_elf_reloca(symtab_section, s, offset, type, c, addend);
}

#if PTR_SIZE == 4
ST_FUNC void greloc(Section *s, Sym *sym, unsigned long offset, int type)
{
    greloca(s, sym, offset, type, 0);
}
#endif

/* ------------------------------------------------------------------------- */
/* symbol allocator */
static Sym *__sym_malloc(void)
{
    Sym *sym_pool, *sym, *last_sym;
    int i;

    sym_pool = tcc_malloc(SYM_POOL_NB * sizeof(Sym));
    dynarray_add(&sym_pools, &nb_sym_pools, sym_pool);

    last_sym = sym_free_first;
    sym = sym_pool;
    for(i = 0; i < SYM_POOL_NB; i++) {
        sym->next = last_sym;
        last_sym = sym;
        sym++;
    }
    sym_free_first = last_sym;
    return last_sym;
}

static inline Sym *sym_malloc(void)
{
    Sym *sym;
#ifndef SYM_DEBUG
    sym = sym_free_first;
    if (!sym)
        sym = __sym_malloc();
    sym_free_first = sym->next;
    return sym;
#else
    sym = tcc_malloc(sizeof(Sym));
    return sym;
#endif
}

ST_INLN void sym_free(Sym *sym)
{
#ifndef SYM_DEBUG
    sym->next = sym_free_first;
    sym_free_first = sym;
#else
    tcc_free(sym);
#endif
}

/* push, without hashing */
ST_FUNC Sym *sym_push2(Sym **ps, int v, int t, int c)
{
    Sym *s;

    s = sym_malloc();
    memset(s, 0, sizeof *s);
    s->v = v;
    s->type.t = t;
    s->c = c;
    /* add in stack */
    s->prev = *ps;
    *ps = s;
    return s;
}

/* find a symbol and return its associated structure. 's' is the top
   of the symbol stack */
ST_FUNC Sym *sym_find2(Sym *s, int v)
{
    while (s) {
        if (s->v == v)
            return s;
        else if (s->v == -1)
            return NULL;
        s = s->prev;
    }
    return NULL;
}

/* structure lookup */
ST_INLN Sym *struct_find(int v)
{
    v -= TOK_IDENT;
    if ((unsigned)v >= (unsigned)(tok_ident - TOK_IDENT))
        return NULL;
    return table_ident[v]->sym_struct;
}

/* find an identifier */
ST_INLN Sym *sym_find(int v)
{
    v -= TOK_IDENT;
    if ((unsigned)v >= (unsigned)(tok_ident - TOK_IDENT))
        return NULL;
    return table_ident[v]->sym_identifier;
}

/* push a given symbol on the symbol stack */
ST_FUNC Sym *sym_push(int v, CType *type, int r, int c)
{
    Sym *s, **ps;
    TokenSym *ts;

    if (local_stack)
        ps = &local_stack;
    else
        ps = &global_stack;
    s = sym_push2(ps, v, type->t, c);
    s->type.ref = type->ref;
    s->r = r;
    /* don't record fields or anonymous symbols */
    /* XXX: simplify */
    if (!(v & SYM_FIELD) && (v & ~SYM_STRUCT) < SYM_FIRST_ANOM) {
        /* record symbol in token array */
        ts = table_ident[(v & ~SYM_STRUCT) - TOK_IDENT];
        if (v & SYM_STRUCT)
            ps = &ts->sym_struct;
        else
            ps = &ts->sym_identifier;
        s->prev_tok = *ps;
        *ps = s;
        s->sym_scope = local_scope;
        if (s->prev_tok && s->prev_tok->sym_scope == s->sym_scope)
            tcc_error(-1, "redeclaration of '%s'", get_tok_str(v & ~SYM_STRUCT, NULL));
    }
    return s;
}

/* push a global identifier */
ST_FUNC Sym *global_identifier_push(int v, int t, int c)
{
    Sym *s, **ps;
    s = sym_push2(&global_stack, v, t, c);
    /* don't record anonymous symbol */
    if (v < SYM_FIRST_ANOM) {
        ps = &table_ident[v - TOK_IDENT]->sym_identifier;
        /* modify the top most local identifier, so that
           sym_identifier will point to 's' when popped */
        while (*ps != NULL && (*ps)->sym_scope)
            ps = &(*ps)->prev_tok;
        s->prev_tok = *ps;
        *ps = s;
    }
    return s;
}

/* pop symbols until top reaches 'b'.  If KEEP is non-zero don't really
   pop them yet from the list, but do remove them from the token array.  */
ST_FUNC void sym_pop(Sym **ptop, Sym *b, int keep)
{
    Sym *s, *ss, **ps;
    TokenSym *ts;
    int v;

    s = *ptop;
    while(s != b) {
        ss = s->prev;
        v = s->v;
        /* remove symbol in token array */
        /* XXX: simplify */
        if (!(v & SYM_FIELD) && (v & ~SYM_STRUCT) < SYM_FIRST_ANOM) {
            ts = table_ident[(v & ~SYM_STRUCT) - TOK_IDENT];
            if (v & SYM_STRUCT)
                ps = &ts->sym_struct;
            else
                ps = &ts->sym_identifier;
            *ps = s->prev_tok;
        }
	if (!keep)
	    sym_free(s);
        s = ss;
    }
    if (!keep)
	*ptop = b;
}

/* ------------------------------------------------------------------------- */

static void vsetc(CType *type, int r, CValue *vc)
{
    int v;

    if( vtop >= vstack + ( VSTACK_SIZE - 1 ))  tcc_error(-1, "memory full (vstack)");
    /* cannot let cpu flags if other instruction are generated. Also
       avoid leaving VT_JMP anywhere except on the top of the stack
       because it would complicate the code generator.

       Don't do this when nocode_wanted.  vtop might come from
       !nocode_wanted regions (see 88_codeopt.c) and transforming
       it to a register without actually generating code is wrong
       as their value might still be used for real.  All values
       we push under nocode_wanted will eventually be popped
       again, so that the VT_CMP/VT_JMP value will be in vtop
       when code is unsuppressed again.

       Same logic below in vswap(); */
    if (vtop >= vstack && !nocode_wanted) {
        v = vtop->r & VT_VALMASK;
        if (v == VT_CMP || (v & ~1) == VT_JMP)
            gv(RC_INT);
    }

    vtop++;
    vtop->type = *type;
    vtop->r = r;
    vtop->r2 = VT_CONST;
    vtop->c = *vc;
    vtop->sym = NULL;
}

ST_FUNC void vswap(void)
{
    SValue tmp;
    /* cannot vswap cpu flags. See comment at vsetc() above */
    if (vtop >= vstack && !nocode_wanted) {
        int v = vtop->r & VT_VALMASK;
        if (v == VT_CMP || (v & ~1) == VT_JMP)
            gv(RC_INT);
    }
    tmp = vtop[0];
    vtop[0] = vtop[-1];
    vtop[-1] = tmp;
}

/* pop stack value */
ST_FUNC void vpop(void)
{
    int v;
    v = vtop->r & VT_VALMASK;
#if defined(TCC_TARGET_I386) || defined(TCC_TARGET_X86_64)
    /* for x86, we need to pop the FP stack */
    if (v == TREG_ST0) {
        o(0xd8dd); /* fstp %st(0) */
    } else
#endif
    if (v == VT_JMP || v == VT_JMPI) {
        /* need to put correct jump if && or || without test */
        gsym(vtop->c.i);
    }
    vtop--;
}

/* push constant of type "type" with useless value */
ST_FUNC void vpush(CType *type)
{
    vset(type, VT_CONST, 0);
}

/* push integer constant */
ST_FUNC void vpushi(int v)
{
    CValue cval;
    cval.i = v;
    vsetc(&int_type, VT_CONST, &cval);
}

/* push a pointer sized constant */
static void vpushs(addr_t v)
{
  CValue cval;
  cval.i = v;
  vsetc(&size_type, VT_CONST, &cval);
}

/* push arbitrary 64bit constant */
ST_FUNC void vpush64(int ty, unsigned long long v)
{
    CValue cval;
    CType ctype;
    ctype.t = ty;
    ctype.ref = NULL;
    cval.i = v;
    vsetc(&ctype, VT_CONST, &cval);
}

/* push long long constant */
static inline void vpushll(long long v)
{
    vpush64(VT_LLONG, v);
}

ST_FUNC void vset(CType *type, int r, int v)
{
    CValue cval;

    cval.i = v;
    vsetc(type, r, &cval);
}

static void vseti(int r, int v)
{
    CType type;
    type.t = VT_INT;
    type.ref = NULL;
    vset(&type, r, v);
}

ST_FUNC void vpushv(SValue *v)
{
    if( vtop >= vstack + ( VSTACK_SIZE - 1 ))  tcc_error(-1, "memory full (vstack)");
    vtop++;
    *vtop = *v;
}

static void vdup(void)
{
    vpushv(vtop);
}

/* rotate n first stack elements to the bottom
   I1 ... In -> I2 ... In I1 [top is right]
*/
ST_FUNC void vrotb(int n)
{
    int i;
    SValue tmp;

    tmp = vtop[-n + 1];
    for(i=-n+1;i!=0;i++)
        vtop[i] = vtop[i+1];
    vtop[0] = tmp;
}

/* rotate the n elements before entry e towards the top
   I1 ... In ... -> In I1 ... I(n-1) ... [top is right]
 */
ST_FUNC void vrote(SValue *e, int n)
{
    int i;
    SValue tmp;

    tmp = *e;
    for(i = 0;i < n - 1; i++)
        e[-i] = e[-i - 1];
    e[-n + 1] = tmp;
}

/* rotate n first stack elements to the top
   I1 ... In -> In I1 ... I(n-1)  [top is right]
 */
ST_FUNC void vrott(int n)
{
    vrote(vtop, n);
}

/* push a symbol value of TYPE */
static inline void vpushsym(CType *type, Sym *sym)
{
    CValue cval;
    cval.i = 0;
    vsetc(type, VT_CONST | VT_SYM, &cval);
    vtop->sym = sym;
}

/* Return a static symbol pointing to a section */
ST_FUNC Sym *get_sym_ref(CType *type, Section *sec, unsigned long offset, unsigned long size)
{
    int v;
    Sym *sym;

    v = anon_sym++;
    sym = global_identifier_push(v, type->t | VT_STATIC, 0);
    sym->type.ref = type->ref;
    sym->r = VT_CONST | VT_SYM;
    put_extern_sym(sym, sec, offset, size);
    return sym;
}

/* push a reference to a section offset by adding a dummy symbol */
static void vpush_ref(CType *type, Section *sec, unsigned long offset, unsigned long size)
{
    vpushsym(type, get_sym_ref(type, sec, offset, size));  
}

/* define a new external reference to a symbol 'v' of type 'u' */
ST_FUNC Sym *external_global_sym(int v, CType *type, int r)
{
    Sym *s;

    s = sym_find(v);
    if (!s) {
        /* push forward reference */
        s = global_identifier_push(v, type->t | VT_EXTERN, 0);
        s->type.ref = type->ref;
        s->r = r | VT_CONST | VT_SYM;
    } else if (IS_ASM_SYM(s)) {
        s->type.t = type->t | (s->type.t & VT_EXTERN);
        s->type.ref = type->ref;
        update_storage(s);
    }
    return s;
}

/* Merge some type attributes.  */
static void patch_type(Sym *sym, CType *type)
{
    if (!(type->t & VT_EXTERN)) {
        if( !( sym->type.t & VT_EXTERN ))  tcc_error(-1, "redefinition of '%s'", get_tok_str(sym->v, NULL));
        sym->type.t &= ~VT_EXTERN;
    }

    if (IS_ASM_SYM(sym)) {
        /* stay static if both are static */
        sym->type.t = type->t & (sym->type.t | ~VT_STATIC);
        sym->type.ref = type->ref;
    }

    if (!is_compatible_types(&sym->type, type)) {
        tcc_error(-1, "incompatible types for redefinition of '%s'", get_tok_str(sym->v, NULL));

    } else if ((sym->type.t & VT_BTYPE) == VT_FUNC) {
        int static_proto = sym->type.t & VT_STATIC;
        /* warn if static follows non-static function declaration */
        if ((type->t & VT_STATIC) && !static_proto && !(type->t & VT_INLINE))
            tcc_error(0, "static storage ignored for redefinition of '%s'", get_tok_str(sym->v, NULL));

        if (0 == (type->t & VT_EXTERN)) {
            /* put complete type, use static from prototype */
            sym->type.t = (type->t & ~VT_STATIC) | static_proto;
            if (type->t & VT_INLINE)
                sym->type.t = type->t;
            sym->type.ref = type->ref;
        }

    } else {
        if ((sym->type.t & VT_ARRAY) && type->ref->c >= 0) {
            /* set array size if it was omitted in extern declaration */
            if (sym->type.ref->c < 0)
                sym->type.ref->c = type->ref->c;
            else if (sym->type.ref->c != type->ref->c)
                tcc_error(-1, "conflicting type for '%s'", get_tok_str(sym->v, NULL));
        }
        if ((type->t ^ sym->type.t) & VT_STATIC)
            tcc_error(0, "storage mismatch for redefinition of '%s'",
                get_tok_str(sym->v, NULL));
    }
}


/* Merge some storage attributes.  */
static void patch_storage(Sym *sym, AttributeDef *ad, CType *type)
{
    if (type)
        patch_type(sym, type);

#ifdef TCC_TARGET_PE
    if (sym->a.dllimport != ad->a.dllimport)
        tcc_error(-1, "incompatible dll linkage for redefinition of '%s'", get_tok_str(sym->v, NULL));
    sym->a.dllexport |= ad->a.dllexport;
#endif
    sym->a.weak |= ad->a.weak;
    if (ad->a.visibility) {
        int vis = sym->a.visibility;
        int vis2 = ad->a.visibility;
        if (vis == STV_DEFAULT)
            vis = vis2;
        else if (vis2 != STV_DEFAULT)
            vis = (vis < vis2) ? vis : vis2;
        sym->a.visibility = vis;
    }
    if (ad->a.aligned)
        sym->a.aligned = ad->a.aligned;
    if (ad->asm_label)
        sym->asm_label = ad->asm_label;
    update_storage(sym);
}

/* define a new external reference to a symbol 'v' */
static Sym *external_sym(int v, CType *type, int r, AttributeDef *ad)
{
    Sym *s;
    s = sym_find(v);
    if (!s) {
        /* push forward reference */
        s = sym_push(v, type, r | VT_CONST | VT_SYM, 0);
        s->type.t |= VT_EXTERN;
        s->a = ad->a;
        s->sym_scope = 0;
    } else {
        if (s->type.ref == func_old_type.ref) {
            s->type.ref = type->ref;
            s->r = r | VT_CONST | VT_SYM;
            s->type.t |= VT_EXTERN;
        }
        patch_storage(s, ad, type);
    }
    return s;
}

/* push a reference to global symbol v */
ST_FUNC void vpush_global_sym(CType *type, int v)
{
    vpushsym(type, external_global_sym(v, type, 0));
}

/* save registers up to (vtop - n) stack entry */
ST_FUNC void save_regs(int n)
{
    SValue *p, *p1;
    for(p = vstack, p1 = vtop - n; p <= p1; p++)
        save_reg(p->r);
}

/* save r to the memory stack, and mark it as being free */
ST_FUNC void save_reg(int r)
{
    save_reg_upstack(r, 0);
}

/* save r to the memory stack, and mark it as being free,
   if seen up to (vtop - n) stack entry */
ST_FUNC void save_reg_upstack(int r, int n)
{
    int l, saved, size, align;
    SValue *p, *p1, sv;
    CType *type;

    if ((r &= VT_VALMASK) >= VT_CONST)
        return;
    if (nocode_wanted)
        return;

    /* modify all stack values */
    saved = 0;
    l = 0;
    for(p = vstack, p1 = vtop - n; p <= p1; p++) {
        if ((p->r & VT_VALMASK) == r ||
            ((p->type.t & VT_BTYPE) == VT_LLONG && (p->r2 & VT_VALMASK) == r)) {
            /* must save value on stack if not already done */
            if (!saved) {
                /* NOTE: must reload 'r' because r might be equal to r2 */
                r = p->r & VT_VALMASK;
                /* store register in the stack */
                type = &p->type;
                if ((p->r & VT_LVAL) ||
                    (!is_float(type->t) && (type->t & VT_BTYPE) != VT_LLONG))
#if PTR_SIZE == 8
                    type = &char_pointer_type;
#else
                    type = &int_type;
#endif
                size = type_size(type, &align);
                loc = (loc - size) & -align;
                sv.type.t = type->t;
                sv.r = VT_LOCAL | VT_LVAL;
                sv.c.i = loc;
                store(r, &sv);
#if defined(TCC_TARGET_I386) || defined(TCC_TARGET_X86_64)
                /* x86 specific: need to pop fp register ST0 if saved */
                if (r == TREG_ST0) {
                    o(0xd8dd); /* fstp %st(0) */
                }
#endif
#if PTR_SIZE == 4
                /* special long long case */
                if ((type->t & VT_BTYPE) == VT_LLONG) {
                    sv.c.i += 4;
                    store(p->r2, &sv);
                }
#endif
                l = loc;
                saved = 1;
            }
            /* mark that stack entry as being saved on the stack */
            if (p->r & VT_LVAL) {
                /* also clear the bounded flag because the
                   relocation address of the function was stored in
                   p->c.i */
                p->r = (p->r & ~(VT_VALMASK | VT_BOUNDED)) | VT_LLOCAL;
            } else {
                p->r = lvalue_type(p->type.t) | VT_LOCAL;
            }
            p->r2 = VT_CONST;
            p->c.i = l;
        }
    }
}

#ifdef TCC_TARGET_ARM
/* find a register of class 'rc2' with at most one reference on stack.
 * If none, call get_reg(rc) */
ST_FUNC int get_reg_ex(int rc, int rc2)
{
    int r;
    SValue *p;
    
    for(r=0;r<NB_REGS;r++) {
        if (reg_classes[r] & rc2) {
            int n;
            n=0;
            for(p = vstack; p <= vtop; p++) {
                if ((p->r & VT_VALMASK) == r ||
                    (p->r2 & VT_VALMASK) == r)
                    n++;
            }
            if (n <= 1)
                return r;
        }
    }
    return get_reg(rc);
}
#endif

/* find a free register of class 'rc'. If none, save one register */
ST_FUNC int get_reg(int rc)
{
    int r;
    SValue *p;

    /* find a free register */
    for(r=0;r<NB_REGS;r++) {
        if (reg_classes[r] & rc) {
            if (nocode_wanted)
                return r;
            for(p=vstack;p<=vtop;p++) {
                if ((p->r & VT_VALMASK) == r ||
                    (p->r2 & VT_VALMASK) == r)
                    goto notfound;
            }
            return r;
        }
    notfound: ;
    }
    
    /* no register left : free the first one on the stack (VERY
       IMPORTANT to start from the bottom to ensure that we don't
       spill registers used in gen_opi()) */
    for(p=vstack;p<=vtop;p++) {
        /* look at second register (if long long) */
        r = p->r2 & VT_VALMASK;
        if (r < VT_CONST && (reg_classes[r] & rc))
            goto save_found;
        r = p->r & VT_VALMASK;
        if (r < VT_CONST && (reg_classes[r] & rc)) {
        save_found:
            save_reg(r);
            return r;
        }
    }
    /* Should never comes here */
    return -1;
}

/* move register 's' (of type 't') to 'r', and flush previous value of r to memory
   if needed */
static void move_reg(int r, int s, int t)
{
    SValue sv;

    if (r != s) {
        save_reg(r);
        sv.type.t = t;
        sv.type.ref = NULL;
        sv.r = s;
        sv.c.i = 0;
        load(r, &sv);
    }
}

/* get address of vtop (vtop MUST BE an lvalue) */
ST_FUNC void gaddrof(void)
{
    vtop->r &= ~VT_LVAL;
    /* tricky: if saved lvalue, then we can go back to lvalue */
    if ((vtop->r & VT_VALMASK) == VT_LLOCAL)
        vtop->r = (vtop->r & ~(VT_VALMASK | VT_LVAL_TYPE)) | VT_LOCAL | VT_LVAL;


}

#ifdef CONFIG_TCC_BCHECK
/* generate lvalue bound code */
static void gbound(void)
{
    int lval_type;
    CType type1;

    vtop->r &= ~VT_MUSTBOUND;
    /* if lvalue, then use checking code before dereferencing */
    if (vtop->r & VT_LVAL) {
        /* if not VT_BOUNDED value, then make one */
        if (!(vtop->r & VT_BOUNDED)) {
            lval_type = vtop->r & (VT_LVAL_TYPE | VT_LVAL);
            /* must save type because we must set it to int to get pointer */
            type1 = vtop->type;
            vtop->type.t = VT_PTR;
            gaddrof();
            vpushi(0);
            gen_bounded_ptr_add();
            vtop->r |= lval_type;
            vtop->type = type1;
        }
        /* then check for dereferencing */
        gen_bounded_ptr_deref();
    }
}
#endif

static void incr_bf_adr(int o)
{
    vtop->type = char_pointer_type;
    gaddrof();
    vpushi(o);
    gen_op('+');
    vtop->type.t = (vtop->type.t & ~(VT_BTYPE|VT_DEFSIGN))
        | (VT_BYTE|VT_UNSIGNED);
    vtop->r = (vtop->r & ~VT_LVAL_TYPE)
        | (VT_LVAL_BYTE|VT_LVAL_UNSIGNED|VT_LVAL);
}

/* single-byte load mode for packed or otherwise unaligned bitfields */
static void load_packed_bf(CType *type, int bit_pos, int bit_size)
{
    int n, o, bits;
    save_reg_upstack(vtop->r, 1);
    vpush64(type->t & VT_BTYPE, 0); // B X
    bits = 0, o = bit_pos >> 3, bit_pos &= 7;
    do {
        vswap(); // X B
        incr_bf_adr(o);
        vdup(); // X B B
        n = 8 - bit_pos;
        if (n > bit_size)
            n = bit_size;
        if (bit_pos)
            vpushi(bit_pos), gen_op(TOK_SHR), bit_pos = 0; // X B Y
        if (n < 8)
            vpushi((1 << n) - 1), gen_op('&');
        gen_cast(type);
        if (bits)
            vpushi(bits), gen_op(TOK_SHL);
        vrotb(3); // B Y X
        gen_op('|'); // B X
        bits += n, bit_size -= n, o = 1;
    } while (bit_size);
    vswap(), vpop();
    if (!(type->t & VT_UNSIGNED)) {
        n = ((type->t & VT_BTYPE) == VT_LLONG ? 64 : 32) - bits;
        vpushi(n), gen_op(TOK_SHL);
        vpushi(n), gen_op(TOK_SAR);
    }
}

/* single-byte store mode for packed or otherwise unaligned bitfields */
static void store_packed_bf(int bit_pos, int bit_size)
{
    int bits, n, o, m, c;

    c = (vtop->r & (VT_VALMASK | VT_LVAL | VT_SYM)) == VT_CONST;
    vswap(); // X B
    save_reg_upstack(vtop->r, 1);
    bits = 0, o = bit_pos >> 3, bit_pos &= 7;
    do {
        incr_bf_adr(o); // X B
        vswap(); //B X
        c ? vdup() : gv_dup(); // B V X
        vrott(3); // X B V
        if (bits)
            vpushi(bits), gen_op(TOK_SHR);
        if (bit_pos)
            vpushi(bit_pos), gen_op(TOK_SHL);
        n = 8 - bit_pos;
        if (n > bit_size)
            n = bit_size;
        if (n < 8) {
            m = ((1 << n) - 1) << bit_pos;
            vpushi(m), gen_op('&'); // X B V1
            vpushv(vtop-1); // X B V1 B
            vpushi(m & 0x80 ? ~m & 0x7f : ~m);
            gen_op('&'); // X B V1 B1
            gen_op('|'); // X B V2
        }
        vdup(), vtop[-1] = vtop[-2]; // X B B V2
        vstore(), vpop(); // X B
        bits += n, bit_size -= n, bit_pos = 0, o = 1;
    } while (bit_size);
    vpop(), vpop();
}

static int adjust_bf(SValue *sv, int bit_pos, int bit_size)
{
    int t;
    if (0 == sv->type.ref)
        return 0;
    t = sv->type.ref->auxtype;
    if (t != -1 && t != VT_STRUCT) {
        sv->type.t = (sv->type.t & ~VT_BTYPE) | t;
        sv->r = (sv->r & ~VT_LVAL_TYPE) | lvalue_type(sv->type.t);
    }
    return t;
}

/* store vtop a register belonging to class 'rc'. lvalues are
   converted to values. Cannot be used if cannot be converted to
   register value (such as structures). */
ST_FUNC int gv(int rc)
{
    int r, bit_pos, bit_size, size, align, rc2;

    /* NOTE: get_reg can modify vstack[] */
    if (vtop->type.t & VT_BITFIELD) {
        CType type;

        bit_pos = BIT_POS(vtop->type.t);
        bit_size = BIT_SIZE(vtop->type.t);
        /* remove bit field info to avoid loops */
        vtop->type.t &= ~VT_STRUCT_MASK;

        type.ref = NULL;
        type.t = vtop->type.t & VT_UNSIGNED;
        if ((vtop->type.t & VT_BTYPE) == VT_BOOL)
            type.t |= VT_UNSIGNED;

        r = adjust_bf(vtop, bit_pos, bit_size);

        if ((vtop->type.t & VT_BTYPE) == VT_LLONG)
            type.t |= VT_LLONG;
        else
            type.t |= VT_INT;

        if (r == VT_STRUCT) {
            load_packed_bf(&type, bit_pos, bit_size);
        } else {
            int bits = (type.t & VT_BTYPE) == VT_LLONG ? 64 : 32;
            /* cast to int to propagate signedness in following ops */
            gen_cast(&type);
            /* generate shifts */
            vpushi(bits - (bit_pos + bit_size));
            gen_op(TOK_SHL);
            vpushi(bits - bit_size);
            /* NOTE: transformed to SHR if unsigned */
            gen_op(TOK_SAR);
        }
        r = gv(rc);
    } else {
        if (is_float(vtop->type.t) && 
            (vtop->r & (VT_VALMASK | VT_LVAL)) == VT_CONST) {
            unsigned long offset;
            /* CPUs usually cannot use float constants, so we store them
               generically in data segment */
            size = type_size(&vtop->type, &align);
            if (NODATA_WANTED)
                size = 0, align = 1;
            offset = section_add(data_section, size, align);
            vpush_ref(&vtop->type, data_section, offset, size);
	    vswap();
	    init_putv(&vtop->type, data_section, offset);
	    vtop->r |= VT_LVAL;
        }
#ifdef CONFIG_TCC_BCHECK
        if (vtop->r & VT_MUSTBOUND) 
            gbound();
#endif

        r = vtop->r & VT_VALMASK;
        rc2 = (rc & RC_FLOAT) ? RC_FLOAT : RC_INT;
#ifndef TCC_TARGET_ARM64
        if (rc == RC_IRET)
            rc2 = RC_LRET;
#ifdef TCC_TARGET_X86_64
        else if (rc == RC_FRET)
            rc2 = RC_QRET;
#endif
#endif
        /* need to reload if:
           - constant
           - lvalue (need to dereference pointer)
           - already a register, but not in the right class */
        if (r >= VT_CONST
         || (vtop->r & VT_LVAL)
         || !(reg_classes[r] & rc)
#if PTR_SIZE == 8
         || ((vtop->type.t & VT_BTYPE) == VT_QLONG && !(reg_classes[vtop->r2] & rc2))
         || ((vtop->type.t & VT_BTYPE) == VT_QFLOAT && !(reg_classes[vtop->r2] & rc2))
#else
         || ((vtop->type.t & VT_BTYPE) == VT_LLONG && !(reg_classes[vtop->r2] & rc2))
#endif
            )
        {
            r = get_reg(rc);
#if PTR_SIZE == 8
            if (((vtop->type.t & VT_BTYPE) == VT_QLONG) || ((vtop->type.t & VT_BTYPE) == VT_QFLOAT)) {
                int addr_type = VT_LLONG, load_size = 8, load_type = ((vtop->type.t & VT_BTYPE) == VT_QLONG) ? VT_LLONG : VT_DOUBLE;
#else
            if ((vtop->type.t & VT_BTYPE) == VT_LLONG) {
                int addr_type = VT_INT, load_size = 4, load_type = VT_INT;
                unsigned long long ll;
#endif
                int r2, original_type;
                original_type = vtop->type.t;
                /* two register type load : expand to two words
                   temporarily */
#if PTR_SIZE == 4
                if ((vtop->r & (VT_VALMASK | VT_LVAL)) == VT_CONST) {
                    /* load constant */
                    ll = vtop->c.i;
                    vtop->c.i = ll; /* first word */
                    load(r, vtop);
                    vtop->r = r; /* save register value */
                    vpushi(ll >> 32); /* second word */
                } else
#endif
                if (vtop->r & VT_LVAL) {
                    /* We do not want to modifier the long long
                       pointer here, so the safest (and less
                       efficient) is to save all the other registers
                       in the stack. XXX: totally inefficient. */
               #if 0
                    save_regs(1);
               #else
                    /* lvalue_save: save only if used further down the stack */
                    save_reg_upstack(vtop->r, 1);
               #endif
                    /* load from memory */
                    vtop->type.t = load_type;
                    load(r, vtop);
                    vdup();
                    vtop[-1].r = r; /* save register value */
                    /* increment pointer to get second word */
                    vtop->type.t = addr_type;
                    gaddrof();
                    vpushi(load_size);
                    gen_op('+');
                    vtop->r |= VT_LVAL;
                    vtop->type.t = load_type;
                } else {
                    /* move registers */
                    load(r, vtop);
                    vdup();
                    vtop[-1].r = r; /* save register value */
                    vtop->r = vtop[-1].r2;
                }
                /* Allocate second register. Here we rely on the fact that
                   get_reg() tries first to free r2 of an SValue. */
                r2 = get_reg(rc2);
                load(r2, vtop);
                vpop();
                /* write second register */
                vtop->r2 = r2;
                vtop->type.t = original_type;
            } else if ((vtop->r & VT_LVAL) && !is_float(vtop->type.t)) {
                int t1, t;
                /* lvalue of scalar type : need to use lvalue type
                   because of possible cast */
                t = vtop->type.t;
                t1 = t;
                /* compute memory access type */
                if (vtop->r & VT_LVAL_BYTE)
                    t = VT_BYTE;
                else if (vtop->r & VT_LVAL_SHORT)
                    t = VT_SHORT;
                if (vtop->r & VT_LVAL_UNSIGNED)
                    t |= VT_UNSIGNED;
                vtop->type.t = t;
                load(r, vtop);
                /* restore wanted type */
                vtop->type.t = t1;
            } else {
                /* one register type load */
                load(r, vtop);
            }
        }
        vtop->r = r;
#ifdef TCC_TARGET_C67
        /* uses register pairs for doubles */
        if ((vtop->type.t & VT_BTYPE) == VT_DOUBLE) 
            vtop->r2 = r+1;
#endif
    }
    return r;
}

/* generate vtop[-1] and vtop[0] in resp. classes rc1 and rc2 */
ST_FUNC void gv2(int rc1, int rc2)
{
    int v;

    /* generate more generic register first. But VT_JMP or VT_CMP
       values must be generated first in all cases to avoid possible
       reload errors */
    v = vtop[0].r & VT_VALMASK;
    if (v != VT_CMP && (v & ~1) != VT_JMP && rc1 <= rc2) {
        vswap();
        gv(rc1);
        vswap();
        gv(rc2);
        /* test if reload is needed for first register */
        if ((vtop[-1].r & VT_VALMASK) >= VT_CONST) {
            vswap();
            gv(rc1);
            vswap();
        }
    } else {
        gv(rc2);
        vswap();
        gv(rc1);
        vswap();
        /* test if reload is needed for first register */
        if ((vtop[0].r & VT_VALMASK) >= VT_CONST) {
            gv(rc2);
        }
    }
}

#ifndef TCC_TARGET_ARM64
/* wrapper around RC_FRET to return a register by type */
static int rc_fret(int t)
{
#ifdef TCC_TARGET_X86_64
    if (t == VT_LDOUBLE) {
        return RC_ST0;
    }
#endif
    return RC_FRET;
}
#endif

/* wrapper around REG_FRET to return a register by type */
static int reg_fret(int t)
{
#ifdef TCC_TARGET_X86_64
    if (t == VT_LDOUBLE) {
        return TREG_ST0;
    }
#endif
    return REG_FRET;
}

#if PTR_SIZE == 4
/* expand 64bit on stack in two ints */
static void lexpand(void)
{
    int u, v;
    u = vtop->type.t & (VT_DEFSIGN | VT_UNSIGNED);
    v = vtop->r & (VT_VALMASK | VT_LVAL);
    if (v == VT_CONST) {
        vdup();
        vtop[0].c.i >>= 32;
    } else if (v == (VT_LVAL|VT_CONST) || v == (VT_LVAL|VT_LOCAL)) {
        vdup();
        vtop[0].c.i += 4;
    } else {
        gv(RC_INT);
        vdup();
        vtop[0].r = vtop[-1].r2;
        vtop[0].r2 = vtop[-1].r2 = VT_CONST;
    }
    vtop[0].type.t = vtop[-1].type.t = VT_INT | u;
}
#endif

#ifdef TCC_TARGET_ARM
/* expand long long on stack */
ST_FUNC void lexpand_nr(void)
{
    int u,v;

    u = vtop->type.t & (VT_DEFSIGN | VT_UNSIGNED);
    vdup();
    vtop->r2 = VT_CONST;
    vtop->type.t = VT_INT | u;
    v=vtop[-1].r & (VT_VALMASK | VT_LVAL);
    if (v == VT_CONST) {
      vtop[-1].c.i = vtop->c.i;
      vtop->c.i = vtop->c.i >> 32;
      vtop->r = VT_CONST;
    } else if (v == (VT_LVAL|VT_CONST) || v == (VT_LVAL|VT_LOCAL)) {
      vtop->c.i += 4;
      vtop->r = vtop[-1].r;
    } else if (v > VT_CONST) {
      vtop--;
      lexpand();
    } else
      vtop->r = vtop[-1].r2;
    vtop[-1].r2 = VT_CONST;
    vtop[-1].type.t = VT_INT | u;
}
#endif

#if PTR_SIZE == 4
/* build a long long from two ints */
static void lbuild(int t)
{
    gv2(RC_INT, RC_INT);
    vtop[-1].r2 = vtop[0].r;
    vtop[-1].type.t = t;
    vpop();
}
#endif

/* convert stack entry to register and duplicate its value in another
   register */
static void gv_dup(void)
{
    int rc, t, r, r1;
    SValue sv;

    t = vtop->type.t;
#if PTR_SIZE == 4
    if ((t & VT_BTYPE) == VT_LLONG) {
        if (t & VT_BITFIELD) {
            gv(RC_INT);
            t = vtop->type.t;
        }
        lexpand();
        gv_dup();
        vswap();
        vrotb(3);
        gv_dup();
        vrotb(4);
        /* stack: H L L1 H1 */
        lbuild(t);
        vrotb(3);
        vrotb(3);
        vswap();
        lbuild(t);
        vswap();
    } else
#endif
    {
        /* duplicate value */
        rc = RC_INT;
        sv.type.t = VT_INT;
        if (is_float(t)) {
            rc = RC_FLOAT;
#ifdef TCC_TARGET_X86_64
            if ((t & VT_BTYPE) == VT_LDOUBLE) {
                rc = RC_ST0;
            }
#endif
            sv.type.t = t;
        }
        r = gv(rc);
        r1 = get_reg(rc);
        sv.r = r;
        sv.c.i = 0;
        load(r1, &sv); /* move r to r1 */
        vdup();
        /* duplicates value */
        if (r != r1)
            vtop->r = r1;
    }
}

/* Generate value test
 *
 * Generate a test for any value (jump, comparison and integers) */
ST_FUNC int gvtst(int inv, int t)
{
    int v = vtop->r & VT_VALMASK;
    if (v != VT_CMP && v != VT_JMP && v != VT_JMPI) {
        vpushi(0);
        gen_op(TOK_NE);
    }
    if ((vtop->r & (VT_VALMASK | VT_LVAL | VT_SYM)) == VT_CONST) {
        /* constant jmp optimization */
        if ((vtop->c.i != 0) != inv)
            t = gjmp(t);
        vtop--;
        return t;
    }
    return gtst(inv, t);
}

#if PTR_SIZE == 4
/* generate CPU independent (unsigned) long long operations */
static void gen_opl(int op)
{
    int t, a, b, op1, c, i;
    int func;
    unsigned short reg_iret = REG_IRET;
    unsigned short reg_lret = REG_LRET;
    SValue tmp;

    switch(op) {
    case '/':
    case TOK_PDIV:
        func = TOK___divdi3;
        goto gen_func;
    case TOK_UDIV:
        func = TOK___udivdi3;
        goto gen_func;
    case '%':
        func = TOK___moddi3;
        goto gen_mod_func;
    case TOK_UMOD:
        func = TOK___umoddi3;
    gen_mod_func:
#ifdef TCC_ARM_EABI
        reg_iret = TREG_R2;
        reg_lret = TREG_R3;
#endif
    gen_func:
        /* call generic long long function */
        vpush_global_sym(&func_old_type, func);
        vrott(3);
        gfunc_call(2);
        vpushi(0);
        vtop->r = reg_iret;
        vtop->r2 = reg_lret;
        break;
    case '^':
    case '&':
    case '|':
    case '*':
    case '+':
    case '-':
        //pv("gen_opl A",0,2);
        t = vtop->type.t;
        vswap();
        lexpand();
        vrotb(3);
        lexpand();
        /* stack: L1 H1 L2 H2 */
        tmp = vtop[0];
        vtop[0] = vtop[-3];
        vtop[-3] = tmp;
        tmp = vtop[-2];
        vtop[-2] = vtop[-3];
        vtop[-3] = tmp;
        vswap();
        /* stack: H1 H2 L1 L2 */
        //pv("gen_opl B",0,4);
        if (op == '*') {
            vpushv(vtop - 1);
            vpushv(vtop - 1);
            gen_op(TOK_UMULL);
            lexpand();
            /* stack: H1 H2 L1 L2 ML MH */
            for(i=0;i<4;i++)
                vrotb(6);
            /* stack: ML MH H1 H2 L1 L2 */
            tmp = vtop[0];
            vtop[0] = vtop[-2];
            vtop[-2] = tmp;
            /* stack: ML MH H1 L2 H2 L1 */
            gen_op('*');
            vrotb(3);
            vrotb(3);
            gen_op('*');
            /* stack: ML MH M1 M2 */
            gen_op('+');
            gen_op('+');
        } else if (op == '+' || op == '-') {
            /* XXX: add non carry method too (for MIPS or alpha) */
            if (op == '+')
                op1 = TOK_ADDC1;
            else
                op1 = TOK_SUBC1;
            gen_op(op1);
            /* stack: H1 H2 (L1 op L2) */
            vrotb(3);
            vrotb(3);
            gen_op(op1 + 1); /* TOK_xxxC2 */
        } else {
            gen_op(op);
            /* stack: H1 H2 (L1 op L2) */
            vrotb(3);
            vrotb(3);
            /* stack: (L1 op L2) H1 H2 */
            gen_op(op);
            /* stack: (L1 op L2) (H1 op H2) */
        }
        /* stack: L H */
        lbuild(t);
        break;
    case TOK_SAR:
    case TOK_SHR:
    case TOK_SHL:
        if ((vtop->r & (VT_VALMASK | VT_LVAL | VT_SYM)) == VT_CONST) {
            t = vtop[-1].type.t;
            vswap();
            lexpand();
            vrotb(3);
            /* stack: L H shift */
            c = (int)vtop->c.i;
            /* constant: simpler */
            /* NOTE: all comments are for SHL. the other cases are
               done by swapping words */
            vpop();
            if (op != TOK_SHL)
                vswap();
            if (c >= 32) {
                /* stack: L H */
                vpop();
                if (c > 32) {
                    vpushi(c - 32);
                    gen_op(op);
                }
                if (op != TOK_SAR) {
                    vpushi(0);
                } else {
                    gv_dup();
                    vpushi(31);
                    gen_op(TOK_SAR);
                }
                vswap();
            } else {
                vswap();
                gv_dup();
                /* stack: H L L */
                vpushi(c);
                gen_op(op);
                vswap();
                vpushi(32 - c);
                if (op == TOK_SHL)
                    gen_op(TOK_SHR);
                else
                    gen_op(TOK_SHL);
                vrotb(3);
                /* stack: L L H */
                vpushi(c);
                if (op == TOK_SHL)
                    gen_op(TOK_SHL);
                else
                    gen_op(TOK_SHR);
                gen_op('|');
            }
            if (op != TOK_SHL)
                vswap();
            lbuild(t);
        } else {
            /* XXX: should provide a faster fallback on x86 ? */
            switch(op) {
            case TOK_SAR:
                func = TOK___ashrdi3;
                goto gen_func;
            case TOK_SHR:
                func = TOK___lshrdi3;
                goto gen_func;
            case TOK_SHL:
                func = TOK___ashldi3;
                goto gen_func;
            }
        }
        break;
    default:
        /* compare operations */
        t = vtop->type.t;
        vswap();
        lexpand();
        vrotb(3);
        lexpand();
        /* stack: L1 H1 L2 H2 */
        tmp = vtop[-1];
        vtop[-1] = vtop[-2];
        vtop[-2] = tmp;
        /* stack: L1 L2 H1 H2 */
        /* compare high */
        op1 = op;
        /* when values are equal, we need to compare low words. since
           the jump is inverted, we invert the test too. */
        if (op1 == TOK_LT)
            op1 = TOK_LE;
        else if (op1 == TOK_GT)
            op1 = TOK_GE;
        else if (op1 == TOK_ULT)
            op1 = TOK_ULE;
        else if (op1 == TOK_UGT)
            op1 = TOK_UGE;
        a = 0;
        b = 0;
        gen_op(op1);
        if (op == TOK_NE) {
            b = gvtst(0, 0);
        } else {
            a = gvtst(1, 0);
            if (op != TOK_EQ) {
                /* generate non equal test */
                vpushi(TOK_NE);
                vtop->r = VT_CMP;
                b = gvtst(0, 0);
            }
        }
        /* compare low. Always unsigned */
        op1 = op;
        if (op1 == TOK_LT)
            op1 = TOK_ULT;
        else if (op1 == TOK_LE)
            op1 = TOK_ULE;
        else if (op1 == TOK_GT)
            op1 = TOK_UGT;
        else if (op1 == TOK_GE)
            op1 = TOK_UGE;
        gen_op(op1);
        a = gvtst(1, a);
        gsym(b);
        vseti(VT_JMPI, a);
        break;
    }
}
#endif

static uint64_t gen_opic_sdiv(uint64_t a, uint64_t b)
{
    uint64_t x = (a >> 63 ? -a : a) / (b >> 63 ? -b : b);
    return (a ^ b) >> 63 ? -x : x;
}

static int gen_opic_lt(uint64_t a, uint64_t b)
{
    return (a ^ (uint64_t)1 << 63) < (b ^ (uint64_t)1 << 63);
}

/* handle integer constant optimizations and various machine
   independent opt */
static void gen_opic(int op)
{
    SValue *v1 = vtop - 1;
    SValue *v2 = vtop;
    int t1 = v1->type.t & VT_BTYPE;
    int t2 = v2->type.t & VT_BTYPE;
    int c1 = (v1->r & (VT_VALMASK | VT_LVAL | VT_SYM)) == VT_CONST;
    int c2 = (v2->r & (VT_VALMASK | VT_LVAL | VT_SYM)) == VT_CONST;
    uint64_t l1 = c1 ? v1->c.i : 0;
    uint64_t l2 = c2 ? v2->c.i : 0;
    int shm = (t1 == VT_LLONG) ? 63 : 31;

    if (t1 != VT_LLONG && (PTR_SIZE != 8 || t1 != VT_PTR))
        l1 = ((uint32_t)l1 |
              (v1->type.t & VT_UNSIGNED ? 0 : -(l1 & 0x80000000)));
    if (t2 != VT_LLONG && (PTR_SIZE != 8 || t2 != VT_PTR))
        l2 = ((uint32_t)l2 |
              (v2->type.t & VT_UNSIGNED ? 0 : -(l2 & 0x80000000)));

    if (c1 && c2) {
        switch(op) {
        case '+': l1 += l2; break;
        case '-': l1 -= l2; break;
        case '&': l1 &= l2; break;
        case '^': l1 ^= l2; break;
        case '|': l1 |= l2; break;
        case '*': l1 *= l2; break;

        case TOK_PDIV:
        case '/':
        case '%':
        case TOK_UDIV:
        case TOK_UMOD:
            /* if division by zero, generate explicit division */
            if (l2 == 0) {
                if (const_wanted)
                    tcc_error(-1, "division by zero in constant");
                goto general_case;
            }
            switch(op) {
            default: l1 = gen_opic_sdiv(l1, l2); break;
            case '%': l1 = l1 - l2 * gen_opic_sdiv(l1, l2); break;
            case TOK_UDIV: l1 = l1 / l2; break;
            case TOK_UMOD: l1 = l1 % l2; break;
            }
            break;
        case TOK_SHL: l1 <<= (l2 & shm); break;
        case TOK_SHR: l1 >>= (l2 & shm); break;
        case TOK_SAR:
            l1 = (l1 >> 63) ? ~(~l1 >> (l2 & shm)) : l1 >> (l2 & shm);
            break;
            /* tests */
        case TOK_ULT: l1 = l1 < l2; break;
        case TOK_UGE: l1 = l1 >= l2; break;
        case TOK_EQ: l1 = l1 == l2; break;
        case TOK_NE: l1 = l1 != l2; break;
        case TOK_ULE: l1 = l1 <= l2; break;
        case TOK_UGT: l1 = l1 > l2; break;
        case TOK_LT: l1 = gen_opic_lt(l1, l2); break;
        case TOK_GE: l1 = !gen_opic_lt(l1, l2); break;
        case TOK_LE: l1 = !gen_opic_lt(l2, l1); break;
        case TOK_GT: l1 = gen_opic_lt(l2, l1); break;
            /* logical */
        case TOK_LAND: l1 = l1 && l2; break;
        case TOK_LOR: l1 = l1 || l2; break;
        default:
            goto general_case;
        }
	if (t1 != VT_LLONG && (PTR_SIZE != 8 || t1 != VT_PTR))
	    l1 = ((uint32_t)l1 |
		(v1->type.t & VT_UNSIGNED ? 0 : -(l1 & 0x80000000)));
        v1->c.i = l1;
        vtop--;
    } else {
        /* if commutative ops, put c2 as constant */
        if (c1 && (op == '+' || op == '&' || op == '^' || 
                   op == '|' || op == '*')) {
            vswap();
            c2 = c1; //c = c1, c1 = c2, c2 = c;
            l2 = l1; //l = l1, l1 = l2, l2 = l;
        }
        if (!const_wanted &&
            c1 && ((l1 == 0 &&
                    (op == TOK_SHL || op == TOK_SHR || op == TOK_SAR)) ||
                   (l1 == -1 && op == TOK_SAR))) {
            /* treat (0 << x), (0 >> x) and (-1 >> x) as constant */
            vtop--;
        } else if (!const_wanted &&
                   c2 && ((l2 == 0 && (op == '&' || op == '*')) ||
                          (op == '|' &&
                            (l2 == -1 || (l2 == 0xFFFFFFFF && t2 != VT_LLONG))) ||
                          (l2 == 1 && (op == '%' || op == TOK_UMOD)))) {
            /* treat (x & 0), (x * 0), (x | -1) and (x % 1) as constant */
            if (l2 == 1)
                vtop->c.i = 0;
            vswap();
            vtop--;
        } else if (c2 && (((op == '*' || op == '/' || op == TOK_UDIV ||
                          op == TOK_PDIV) &&
                           l2 == 1) ||
                          ((op == '+' || op == '-' || op == '|' || op == '^' ||
                            op == TOK_SHL || op == TOK_SHR || op == TOK_SAR) &&
                           l2 == 0) ||
                          (op == '&' &&
                            (l2 == -1 || (l2 == 0xFFFFFFFF && t2 != VT_LLONG))))) {
            /* filter out NOP operations like x*1, x-0, x&-1... */
            vtop--;
        } else if (c2 && (op == '*' || op == TOK_PDIV || op == TOK_UDIV)) {
            /* try to use shifts instead of muls or divs */
            if (l2 > 0 && (l2 & (l2 - 1)) == 0) {
                int n = -1;
                while (l2) {
                    l2 >>= 1;
                    n++;
                }
                vtop->c.i = n;
                if (op == '*')
                    op = TOK_SHL;
                else if (op == TOK_PDIV)
                    op = TOK_SAR;
                else
                    op = TOK_SHR;
            }
            goto general_case;
        } else if (c2 && (op == '+' || op == '-') &&
                   (((vtop[-1].r & (VT_VALMASK | VT_LVAL | VT_SYM)) == (VT_CONST | VT_SYM))
                    || (vtop[-1].r & (VT_VALMASK | VT_LVAL)) == VT_LOCAL)) {
            /* symbol + constant case */
            if (op == '-')
                l2 = -l2;
	    l2 += vtop[-1].c.i;
	    /* The backends can't always deal with addends to symbols
	       larger than +-1<<31.  Don't construct such.  */
	    if ((int)l2 != l2)
	        goto general_case;
            vtop--;
            vtop->c.i = l2;
        } else {
        general_case:
                /* call low level op generator */
                if (t1 == VT_LLONG || t2 == VT_LLONG ||
                    (PTR_SIZE == 8 && (t1 == VT_PTR || t2 == VT_PTR)))
                    gen_opl(op);
                else
                    gen_opi(op);
        }
    }
}

/* generate a floating point operation with constant propagation */
static void gen_opif(int op)
{
    int c1, c2;
    SValue *v1, *v2;
#if defined _MSC_VER && defined _AMD64_
    /* avoid bad optimization with f1 -= f2 for f1:-0.0, f2:0.0 */
    volatile
#endif
    long double f1, f2;

    v1 = vtop - 1;
    v2 = vtop;
    /* currently, we cannot do computations with forward symbols */
    c1 = (v1->r & (VT_VALMASK | VT_LVAL | VT_SYM)) == VT_CONST;
    c2 = (v2->r & (VT_VALMASK | VT_LVAL | VT_SYM)) == VT_CONST;
    if (c1 && c2) {
        if (v1->type.t == VT_FLOAT) {
            f1 = v1->c.f;
            f2 = v2->c.f;
        } else if (v1->type.t == VT_DOUBLE) {
            f1 = v1->c.d;
            f2 = v2->c.d;
        } else {
            f1 = v1->c.ld;
            f2 = v2->c.ld;
        }

        /* NOTE: we only do constant propagation if finite number (not
           NaN or infinity) (ANSI spec) */
        if (!ieee_finite(f1) || !ieee_finite(f2))
            goto general_case;

        switch(op) {
        case '+': f1 += f2; break;
        case '-': f1 -= f2; break;
        case '*': f1 *= f2; break;
        case '/': 
            if (f2 == 0.0) {
                if( const_wanted )  tcc_error(-1, "division by zero in constant");
                goto general_case;
            }
            f1 /= f2; 
            break;
            /* XXX: also handles tests ? */
        default:
            goto general_case;
        }
        /* XXX: overflow test ? */
        if (v1->type.t == VT_FLOAT) {
            v1->c.f = f1;
        } else if (v1->type.t == VT_DOUBLE) {
            v1->c.d = f1;
        } else {
            v1->c.ld = f1;
        }
        vtop--;
    } else {
    general_case:
        gen_opf(op);
    }
}

static int pointed_size(CType *type)
{
    int align;
    return type_size(pointed_type(type), &align);
}

static void vla_runtime_pointed_size(CType *type)
{
    int align;
    vla_runtime_type_size(pointed_type(type), &align);
}

static inline int is_null_pointer(SValue *p)
{
    if ((p->r & (VT_VALMASK | VT_LVAL | VT_SYM)) != VT_CONST)
        return 0;
    return ((p->type.t & VT_BTYPE) == VT_INT && (uint32_t)p->c.i == 0) ||
        ((p->type.t & VT_BTYPE) == VT_LLONG && p->c.i == 0) ||
        ((p->type.t & VT_BTYPE) == VT_PTR &&
         (PTR_SIZE == 4 ? (uint32_t)p->c.i == 0 : p->c.i == 0));
}

static inline int is_integer_btype(int bt)
{
    return (bt == VT_BYTE || bt == VT_SHORT || 
            bt == VT_INT || bt == VT_LLONG);
}

/* check types for comparison or subtraction of pointers */
static void check_comparison_pointer_types(SValue *p1, SValue *p2, int op)
{
    CType *type1, *type2, tmp_type1, tmp_type2;
    int bt1, bt2;
    
    /* null pointers are accepted for all comparisons as gcc */
    if (is_null_pointer(p1) || is_null_pointer(p2))
        return;
    type1 = &p1->type;
    type2 = &p2->type;
    bt1 = type1->t & VT_BTYPE;
    bt2 = type2->t & VT_BTYPE;
    /* accept comparison between pointer and integer with a warning */
    if ((is_integer_btype(bt1) || is_integer_btype(bt2)) && op != '-') {
        if( op != TOK_LOR && op != TOK_LAND )  tcc_error(0, "comparison between pointer and integer");
        return;
    }

    /* both must be pointers or implicit function pointers */
    if (bt1 == VT_PTR) {
        type1 = pointed_type(type1);
    } else if (bt1 != VT_FUNC) 
        goto invalid_operands;

    if (bt2 == VT_PTR) {
        type2 = pointed_type(type2);
    } else if (bt2 != VT_FUNC) { 
    invalid_operands:
        tcc_error(-1, "invalid operands to binary %s", get_tok_str(op, NULL));
    }
    if ((type1->t & VT_BTYPE) == VT_VOID || 
        (type2->t & VT_BTYPE) == VT_VOID)
        return;
    tmp_type1 = *type1;
    tmp_type2 = *type2;
    tmp_type1.t &= ~(VT_DEFSIGN | VT_UNSIGNED | VT_CONSTANT | VT_VOLATILE);
    tmp_type2.t &= ~(VT_DEFSIGN | VT_UNSIGNED | VT_CONSTANT | VT_VOLATILE);
    if (!is_compatible_types(&tmp_type1, &tmp_type2)) {
        /* gcc-like error if '-' is used */
        if( op == '-' )  goto invalid_operands;
        else  tcc_error(0, "comparison of distinct pointer types lacks a cast");
    }
}

/* generic gen_op: handles types problems */
ST_FUNC void gen_op(int op)
{
    int u, t1, t2, bt1, bt2, t;
    CType type1;

redo:
    t1 = vtop[-1].type.t;
    t2 = vtop[0].type.t;
    bt1 = t1 & VT_BTYPE;
    bt2 = t2 & VT_BTYPE;
        
    if (bt1 == VT_STRUCT || bt2 == VT_STRUCT) {
        tcc_error(-1, "operation on a struct");
    } else if (bt1 == VT_FUNC || bt2 == VT_FUNC) {
	if (bt2 == VT_FUNC) {
	    mk_pointer(&vtop->type);
	    gaddrof();
	}
	if (bt1 == VT_FUNC) {
	    vswap();
	    mk_pointer(&vtop->type);
	    gaddrof();
	    vswap();
	}
	goto redo;
    } else if (bt1 == VT_PTR || bt2 == VT_PTR) {
        /* at least one operand is a pointer */
        /* relational op: must be both pointers */
        if (op >= TOK_ULT && op <= TOK_LOR) {
            check_comparison_pointer_types(vtop - 1, vtop, op);
            /* pointers are handled are unsigned */
#if PTR_SIZE == 8
            t = VT_LLONG | VT_UNSIGNED;
#else
            t = VT_INT | VT_UNSIGNED;
#endif
            goto std_op;
        }
        /* if both pointers, then it must be the '-' op */
        if (bt1 == VT_PTR && bt2 == VT_PTR) {
            if( op != '-' )  tcc_error(-1, "cannot use pointers here");
            check_comparison_pointer_types(vtop - 1, vtop, op);
            /* XXX: check that types are compatible */
            if (vtop[-1].type.t & VT_VLA) {
                vla_runtime_pointed_size(&vtop[-1].type);
            } else {
                vpushi(pointed_size(&vtop[-1].type));
            }
            vrott(3);
            gen_opic(op);
            vtop->type.t = ptrdiff_type.t;
            vswap();
            gen_op(TOK_PDIV);
        } else {
            /* exactly one pointer : must be '+' or '-'. */
            if( op != '-' && op != '+' )  tcc_error(-1, "cannot use pointers here");
            /* Put pointer as first operand */
            if (bt2 == VT_PTR) {
                vswap();
                t = t1, t1 = t2, t2 = t;
            }
#if PTR_SIZE == 4
            if ((vtop[0].type.t & VT_BTYPE) == VT_LLONG)
                /* XXX: truncate here because gen_opl can't handle ptr + long long */
                gen_cast_s(VT_INT);
#endif
            type1 = vtop[-1].type;
            type1.t &= ~VT_ARRAY;
            if (vtop[-1].type.t & VT_VLA)
                vla_runtime_pointed_size(&vtop[-1].type);
            else {
                u = pointed_size(&vtop[-1].type);
                if( u < 0 )  tcc_error(-1, "unknown array element size");
#if PTR_SIZE == 8
                vpushll(u);
#else
                /* XXX: cast to int ? (long long case) */
                vpushi(u);
#endif
            }
            gen_op('*');
            {
                gen_opic(op);
            }
            /* put again type if gen_opic() swaped operands */
            vtop->type = type1;
        }
    } else if (is_float(bt1) || is_float(bt2)) {
        /* compute bigger type and do implicit casts */
        if (bt1 == VT_LDOUBLE || bt2 == VT_LDOUBLE) {
            t = VT_LDOUBLE;
        } else if (bt1 == VT_DOUBLE || bt2 == VT_DOUBLE) {
            t = VT_DOUBLE;
        } else {
            t = VT_FLOAT;
        }
        /* floats can only be used for a few operations */
        if (op != '+' && op != '-' && op != '*' && op != '/' &&
            (op < TOK_ULT || op > TOK_GT))
            tcc_error(-1, "invalid operands for binary operation");
        goto std_op;
    } else if (op == TOK_SHR || op == TOK_SAR || op == TOK_SHL) {
        t = bt1 == VT_LLONG ? VT_LLONG : VT_INT;
        if ((t1 & (VT_BTYPE | VT_UNSIGNED | VT_BITFIELD)) == (t | VT_UNSIGNED))
          t |= VT_UNSIGNED;
        t |= (VT_LONG & t1);
        goto std_op;
    } else if (bt1 == VT_LLONG || bt2 == VT_LLONG) {
        /* cast to biggest op */
        t = VT_LLONG | VT_LONG;
        if (bt1 == VT_LLONG)
            t &= t1;
        if (bt2 == VT_LLONG)
            t &= t2;
        /* convert to unsigned if it does not fit in a long long */
        if ((t1 & (VT_BTYPE | VT_UNSIGNED | VT_BITFIELD)) == (VT_LLONG | VT_UNSIGNED) ||
            (t2 & (VT_BTYPE | VT_UNSIGNED | VT_BITFIELD)) == (VT_LLONG | VT_UNSIGNED))
            t |= VT_UNSIGNED;
        goto std_op;
    } else {
        /* integer operations */
        t = VT_INT | (VT_LONG & (t1 | t2));
        /* convert to unsigned if it does not fit in an integer */
        if ((t1 & (VT_BTYPE | VT_UNSIGNED | VT_BITFIELD)) == (VT_INT | VT_UNSIGNED) ||
            (t2 & (VT_BTYPE | VT_UNSIGNED | VT_BITFIELD)) == (VT_INT | VT_UNSIGNED))
            t |= VT_UNSIGNED;
    std_op:
        /* XXX: currently, some unsigned operations are explicit, so
           we modify them here */
        if (t & VT_UNSIGNED) {
            if (op == TOK_SAR)
                op = TOK_SHR;
            else if (op == '/')
                op = TOK_UDIV;
            else if (op == '%')
                op = TOK_UMOD;
            else if (op == TOK_LT)
                op = TOK_ULT;
            else if (op == TOK_GT)
                op = TOK_UGT;
            else if (op == TOK_LE)
                op = TOK_ULE;
            else if (op == TOK_GE)
                op = TOK_UGE;
        }
        vswap();
        type1.t = t;
        type1.ref = NULL;
        gen_cast(&type1);
        vswap();
        /* special case for shifts and long long: we keep the shift as
           an integer */
        if (op == TOK_SHR || op == TOK_SAR || op == TOK_SHL)
            type1.t = VT_INT;
        gen_cast(&type1);
        if (is_float(t))
            gen_opif(op);
        else
            gen_opic(op);
        if (op >= TOK_ULT && op <= TOK_GT) {
            /* relational op: the result is an int */
            vtop->type.t = VT_INT;
        } else {
            vtop->type.t = t;
        }
    }
    // Make sure that we have converted to an rvalue:
    if (vtop->r & VT_LVAL)
        gv(is_float(vtop->type.t & VT_BTYPE) ? RC_FLOAT : RC_INT);
}

#ifndef TCC_TARGET_ARM
/* generic itof for unsigned long long case */
static void gen_cvt_itof1(int t)
{
#ifdef TCC_TARGET_ARM64
    gen_cvt_itof(t);
#else
    if ((vtop->type.t & (VT_BTYPE | VT_UNSIGNED)) == 
        (VT_LLONG | VT_UNSIGNED)) {

        if (t == VT_FLOAT)
            vpush_global_sym(&func_old_type, TOK___floatundisf);
#if LDOUBLE_SIZE != 8
        else if (t == VT_LDOUBLE)
            vpush_global_sym(&func_old_type, TOK___floatundixf);
#endif
        else
            vpush_global_sym(&func_old_type, TOK___floatundidf);
        vrott(2);
        gfunc_call(1);
        vpushi(0);
        vtop->r = reg_fret(t);
    } else {
        gen_cvt_itof(t);
    }
#endif
}
#endif

/* generic ftoi for unsigned long long case */
static void gen_cvt_ftoi1(int t)
{
#ifdef TCC_TARGET_ARM64
    gen_cvt_ftoi(t);
#else
    int st;

    if (t == (VT_LLONG | VT_UNSIGNED)) {
        /* not handled natively */
        st = vtop->type.t & VT_BTYPE;
        if (st == VT_FLOAT)
            vpush_global_sym(&func_old_type, TOK___fixunssfdi);
#if LDOUBLE_SIZE != 8
        else if (st == VT_LDOUBLE)
            vpush_global_sym(&func_old_type, TOK___fixunsxfdi);
#endif
        else
            vpush_global_sym(&func_old_type, TOK___fixunsdfdi);
        vrott(2);
        gfunc_call(1);
        vpushi(0);
        vtop->r = REG_IRET;
        vtop->r2 = REG_LRET;
    } else {
        gen_cvt_ftoi(t);
    }
#endif
}

/* force char or short cast */
static void force_charshort_cast(int t)
{
    int bits, dbt;

    /* cannot cast static initializers */
    if (STATIC_DATA_WANTED)
	return;

    dbt = t & VT_BTYPE;
    /* XXX: add optimization if lvalue : just change type and offset */
    if (dbt == VT_BYTE)
        bits = 8;
    else
        bits = 16;
    if (t & VT_UNSIGNED) {
        vpushi((1 << bits) - 1);
        gen_op('&');
    } else {
        if ((vtop->type.t & VT_BTYPE) == VT_LLONG)
            bits = 64 - bits;
        else
            bits = 32 - bits;
        vpushi(bits);
        gen_op(TOK_SHL);
        /* result must be signed or the SAR is converted to an SHL
           This was not the case when "t" was a signed short
           and the last value on the stack was an unsigned int */
        vtop->type.t &= ~VT_UNSIGNED;
        vpushi(bits);
        gen_op(TOK_SAR);
    }
}

/* cast 'vtop' to 'type'. Casting to bitfields is forbidden. */
static void gen_cast_s(int t)
{
    CType type;
    type.t = t;
    type.ref = NULL;
    gen_cast(&type);
}

static void gen_cast(CType *type)
{
    int sbt, dbt, sf, df, c, p;

    /* special delayed cast for char/short */
    /* XXX: in some cases (multiple cascaded casts), it may still
       be incorrect */
    if (vtop->r & VT_MUSTCAST) {
        vtop->r &= ~VT_MUSTCAST;
        force_charshort_cast(vtop->type.t);
    }

    /* bitfields first get cast to ints */
    if (vtop->type.t & VT_BITFIELD) {
        gv(RC_INT);
    }

    dbt = type->t & (VT_BTYPE | VT_UNSIGNED);
    sbt = vtop->type.t & (VT_BTYPE | VT_UNSIGNED);

    if (sbt != dbt) {
        sf = is_float(sbt);
        df = is_float(dbt);
        c = (vtop->r & (VT_VALMASK | VT_LVAL | VT_SYM)) == VT_CONST;
        p = (vtop->r & (VT_VALMASK | VT_LVAL | VT_SYM)) == (VT_CONST | VT_SYM);
#if !defined TCC_IS_NATIVE && !defined TCC_IS_NATIVE_387
        c &= dbt != VT_LDOUBLE;
#endif
        if (c) {
            /* constant case: we can do it now */
            /* XXX: in ISOC, cannot do it if error in convert */
            if (sbt == VT_FLOAT)
                vtop->c.ld = vtop->c.f;
            else if (sbt == VT_DOUBLE)
                vtop->c.ld = vtop->c.d;

            if (df) {
                if ((sbt & VT_BTYPE) == VT_LLONG) {
                    if ((sbt & VT_UNSIGNED) || !(vtop->c.i >> 63))
                        vtop->c.ld = vtop->c.i;
                    else
                        vtop->c.ld = -(long double)-vtop->c.i;
                } else if(!sf) {
                    if ((sbt & VT_UNSIGNED) || !(vtop->c.i >> 31))
                        vtop->c.ld = (uint32_t)vtop->c.i;
                    else
                        vtop->c.ld = -(long double)-(uint32_t)vtop->c.i;
                }

                if (dbt == VT_FLOAT)
                    vtop->c.f = (float)vtop->c.ld;
                else if (dbt == VT_DOUBLE)
                    vtop->c.d = (double)vtop->c.ld;
            } else if (sf && dbt == (VT_LLONG|VT_UNSIGNED)) {
                vtop->c.i = vtop->c.ld;
            } else if (sf && dbt == VT_BOOL) {
                vtop->c.i = (vtop->c.ld != 0);
            } else {
                if(sf)
                    vtop->c.i = vtop->c.ld;
                else if (sbt == (VT_LLONG|VT_UNSIGNED))
                    ;
                else if (sbt & VT_UNSIGNED)
                    vtop->c.i = (uint32_t)vtop->c.i;
#if PTR_SIZE == 8
                else if (sbt == VT_PTR)
                    ;
#endif
                else if (sbt != VT_LLONG)
                    vtop->c.i = ((uint32_t)vtop->c.i |
                                  -(vtop->c.i & 0x80000000));

                if (dbt == (VT_LLONG|VT_UNSIGNED))
                    ;
                else if (dbt == VT_BOOL)
                    vtop->c.i = (vtop->c.i != 0);
#if PTR_SIZE == 8
                else if (dbt == VT_PTR)
                    ;
#endif
                else if (dbt != VT_LLONG) {
                    uint32_t m = ((dbt & VT_BTYPE) == VT_BYTE ? 0xff :
                                  (dbt & VT_BTYPE) == VT_SHORT ? 0xffff :
                                  0xffffffff);
                    vtop->c.i &= m;
                    if (!(dbt & VT_UNSIGNED))
                        vtop->c.i |= -(vtop->c.i & ((m >> 1) + 1));
                }
            }
        } else if (p && dbt == VT_BOOL) {
            vtop->r = VT_CONST;
            vtop->c.i = 1;
        } else {
            /* non constant case: generate code */
            if (sf && df) {
                /* convert from fp to fp */
                gen_cvt_ftof(dbt);
            } else if (df) {
                /* convert int to fp */
                gen_cvt_itof1(dbt);
            } else if (sf) {
                /* convert fp to int */
                if (dbt == VT_BOOL) {
                     vpushi(0);
                     gen_op(TOK_NE);
                } else {
                    /* we handle char/short/etc... with generic code */
                    if (dbt != (VT_INT | VT_UNSIGNED) &&
                        dbt != (VT_LLONG | VT_UNSIGNED) &&
                        dbt != VT_LLONG)
                        dbt = VT_INT;
                    gen_cvt_ftoi1(dbt);
                    if (dbt == VT_INT && (type->t & (VT_BTYPE | VT_UNSIGNED)) != dbt) {
                        /* additional cast for char/short... */
                        vtop->type.t = dbt;
                        gen_cast(type);
                    }
                }
#if PTR_SIZE == 4
            } else if ((dbt & VT_BTYPE) == VT_LLONG) {
                if ((sbt & VT_BTYPE) != VT_LLONG) {
                    /* scalar to long long */
                    /* machine independent conversion */
                    gv(RC_INT);
                    /* generate high word */
                    if (sbt == (VT_INT | VT_UNSIGNED)) {
                        vpushi(0);
                        gv(RC_INT);
                    } else {
                        if (sbt == VT_PTR) {
                            /* cast from pointer to int before we apply
                               shift operation, which pointers don't support*/
                            gen_cast_s(VT_INT);
                        }
                        gv_dup();
                        vpushi(31);
                        gen_op(TOK_SAR);
                    }
                    /* patch second register */
                    vtop[-1].r2 = vtop->r;
                    vpop();
                }
#else
            } else if ((dbt & VT_BTYPE) == VT_LLONG ||
                       (dbt & VT_BTYPE) == VT_PTR ||
                       (dbt & VT_BTYPE) == VT_FUNC) {
                if ((sbt & VT_BTYPE) != VT_LLONG &&
                    (sbt & VT_BTYPE) != VT_PTR &&
                    (sbt & VT_BTYPE) != VT_FUNC) {
                    /* need to convert from 32bit to 64bit */
                    gv(RC_INT);
                    if (sbt != (VT_INT | VT_UNSIGNED)) {
#if defined(TCC_TARGET_ARM64)
                        gen_cvt_sxtw();
#elif defined(TCC_TARGET_X86_64)
                        int r = gv(RC_INT);
                        /* x86_64 specific: movslq */
                        o(0x6348);
                        o(0xc0 + (REG_VALUE(r) << 3) + REG_VALUE(r));
#else
#error
#endif
                    }
                }
#endif
            } else if (dbt == VT_BOOL) {
                /* scalar to bool */
                vpushi(0);
                gen_op(TOK_NE);
            } else if ((dbt & VT_BTYPE) == VT_BYTE || 
                       (dbt & VT_BTYPE) == VT_SHORT) {
                if (sbt == VT_PTR) {
                    vtop->type.t = VT_INT;
                    tcc_error(0, "nonportable conversion from pointer to char/short");
                }
                force_charshort_cast(dbt);
#if PTR_SIZE == 4
            } else if ((dbt & VT_BTYPE) == VT_INT) {
                /* scalar to int */
                if ((sbt & VT_BTYPE) == VT_LLONG) {
                    /* from long long: just take low order word */
                    lexpand();
                    vpop();
                } 
                /* if lvalue and single word type, nothing to do because
                   the lvalue already contains the real type size (see
                   VT_LVAL_xxx constants) */
#endif
            }
        }
    } else if ((dbt & VT_BTYPE) == VT_PTR && !(vtop->r & VT_LVAL)) {
        /* if we are casting between pointer types,
           we must update the VT_LVAL_xxx size */
        vtop->r = (vtop->r & ~VT_LVAL_TYPE)
                  | (lvalue_type(type->ref->type.t) & VT_LVAL_TYPE);
    }
    vtop->type = *type;
}

/* return type size as known at compile time. Put alignment at 'a' */
ST_FUNC int type_size(CType *type, int *a)
{
    Sym *s;
    int bt;

    bt = type->t & VT_BTYPE;
    if (bt == VT_STRUCT) {
        /* struct/union */
        s = type->ref;
        *a = s->r;
        return s->c;
    } else if (bt == VT_PTR) {
        if (type->t & VT_ARRAY) {
            int ts;

            s = type->ref;
            ts = type_size(&s->type, a);

            if (ts < 0 && s->c < 0)
                ts = -ts;

            return ts * s->c;
        } else {
            *a = PTR_SIZE;
            return PTR_SIZE;
        }
    } else if (IS_ENUM(type->t) && type->ref->c == -1) {
        return -1; /* incomplete enum */
    } else if (bt == VT_LDOUBLE) {
        *a = LDOUBLE_ALIGN;
        return LDOUBLE_SIZE;
    } else if (bt == VT_DOUBLE || bt == VT_LLONG) {
#ifdef TCC_TARGET_I386
#ifdef TCC_TARGET_PE
        *a = 8;
#else
        *a = 4;
#endif
#elif defined(TCC_TARGET_ARM)
#ifdef TCC_ARM_EABI
        *a = 8; 
#else
        *a = 4;
#endif
#else
        *a = 8;
#endif
        return 8;
    } else if (bt == VT_INT || bt == VT_FLOAT) {
        *a = 4;
        return 4;
    } else if (bt == VT_SHORT) {
        *a = 2;
        return 2;
    } else if (bt == VT_QLONG || bt == VT_QFLOAT) {
        *a = 8;
        return 16;
    } else {
        /* char, void, function, _Bool */
        *a = 1;
        return 1;
    }
}

/* push type size as known at runtime time on top of value stack. Put
   alignment at 'a' */
ST_FUNC void vla_runtime_type_size(CType *type, int *a)
{
    if (type->t & VT_VLA) {
        type_size(&type->ref->type, a);
        vset(&int_type, VT_LOCAL|VT_LVAL, type->ref->c);
    } else {
        vpushi(type_size(type, a));
    }
}

static void vla_sp_restore(void) {
    if (vlas_in_scope) {
        gen_vla_sp_restore(vla_sp_loc);
    }
}

static void vla_sp_restore_root(void) {
    if (vlas_in_scope) {
        gen_vla_sp_restore(vla_sp_root_loc);
    }
}

/* return the pointed type of t */
static inline CType *pointed_type(CType *type)
{
    return &type->ref->type;
}

/* modify type so that its it is a pointer to type. */
ST_FUNC void mk_pointer(CType *type)
{
    Sym *s;
    s = sym_push(SYM_FIELD, type, 0, -1);
    type->t = VT_PTR | (type->t & VT_STORAGE);
    type->ref = s;
}

/* compare function types. OLD functions match any new functions */
static int is_compatible_func(CType *type1, CType *type2)
{
    Sym *s1, *s2;

    s1 = type1->ref;
    s2 = type2->ref;
    if (!is_compatible_types(&s1->type, &s2->type))
        return 0;
    /* check func_call */
    if (s1->f.func_call != s2->f.func_call)
        return 0;
    /* XXX: not complete */
    if (s1->f.func_type == FUNC_OLD || s2->f.func_type == FUNC_OLD)
        return 1;
    if (s1->f.func_type != s2->f.func_type)
        return 0;
    while (s1 != NULL) {
        if (s2 == NULL)
            return 0;
        if (!is_compatible_unqualified_types(&s1->type, &s2->type))
            return 0;
        s1 = s1->next;
        s2 = s2->next;
    }
    if (s2)
        return 0;
    return 1;
}

/* return true if type1 and type2 are the same.  If unqualified is
   true, qualifiers on the types are ignored.

   - enums are not checked as gcc __builtin_types_compatible_p () 
 */
static int compare_types(CType *type1, CType *type2, int unqualified)
{
    int bt1, t1, t2;

    t1 = type1->t & VT_TYPE;
    t2 = type2->t & VT_TYPE;
    if (unqualified) {
        /* strip qualifiers before comparing */
        t1 &= ~(VT_CONSTANT | VT_VOLATILE);
        t2 &= ~(VT_CONSTANT | VT_VOLATILE);
    }

    /* Default Vs explicit signedness only matters for char */
    if ((t1 & VT_BTYPE) != VT_BYTE) {
        t1 &= ~VT_DEFSIGN;
        t2 &= ~VT_DEFSIGN;
    }
    /* XXX: bitfields ? */
    if (t1 != t2)
        return 0;
    /* test more complicated cases */
    bt1 = t1 & VT_BTYPE;
    if (bt1 == VT_PTR) {
        type1 = pointed_type(type1);
        type2 = pointed_type(type2);
        return is_compatible_types(type1, type2);
    } else if (bt1 == VT_STRUCT) {
        return (type1->ref == type2->ref);
    } else if (bt1 == VT_FUNC) {
        return is_compatible_func(type1, type2);
    } else {
        return 1;
    }
}

/* return true if type1 and type2 are exactly the same (including
   qualifiers). 
*/
static int is_compatible_types(CType *type1, CType *type2)
{
    return compare_types(type1,type2,0);
}

/* return true if type1 and type2 are the same (ignoring qualifiers).
*/
static int is_compatible_unqualified_types(CType *type1, CType *type2)
{
    return compare_types(type1,type2,1);
}

/* print a type. If 'varstr' is not NULL, then the variable is also
   printed in the type */
/* XXX: union */
/* XXX: add array and function pointers */
static void type_to_str(char *buf, int buf_size, 
                 CType *type, const char *varstr)
{
    int bt, v, t;
    Sym *s, *sa;
    char buf1[256];
    const char *tstr;

    t = type->t;
    bt = t & VT_BTYPE;
    buf[0] = '\0';

    if (t & VT_EXTERN)
        pstrcat(buf, buf_size, "extern ");
    if (t & VT_STATIC)
        pstrcat(buf, buf_size, "static ");
    if (t & VT_TYPEDEF)
        pstrcat(buf, buf_size, "typedef ");
    if (t & VT_INLINE)
        pstrcat(buf, buf_size, "inline ");
    if (t & VT_VOLATILE)
        pstrcat(buf, buf_size, "volatile ");
    if (t & VT_CONSTANT)
        pstrcat(buf, buf_size, "const ");

    if (((t & VT_DEFSIGN) && bt == VT_BYTE)
        || ((t & VT_UNSIGNED)
            && (bt == VT_SHORT || bt == VT_INT || bt == VT_LLONG)
            && !IS_ENUM(t)
            ))
        pstrcat(buf, buf_size, (t & VT_UNSIGNED) ? "unsigned " : "signed ");

    buf_size -= strlen(buf);
    buf += strlen(buf);

    switch(bt) {
    case VT_VOID:
        tstr = "void";
        goto add_tstr;
    case VT_BOOL:
        tstr = "_Bool";
        goto add_tstr;
    case VT_BYTE:
        tstr = "char";
        goto add_tstr;
    case VT_SHORT:
        tstr = "short";
        goto add_tstr;
    case VT_INT:
        tstr = "int";
        goto maybe_long;
    case VT_LLONG:
        tstr = "long long";
    maybe_long:
        if (t & VT_LONG)
            tstr = "long";
        if (!IS_ENUM(t))
            goto add_tstr;
        tstr = "enum ";
        goto tstruct;
    case VT_FLOAT:
        tstr = "float";
        goto add_tstr;
    case VT_DOUBLE:
        tstr = "double";
        goto add_tstr;
    case VT_LDOUBLE:
        tstr = "long double";
    add_tstr:
        pstrcat(buf, buf_size, tstr);
        break;
    case VT_STRUCT:
        tstr = "struct ";
        if (IS_UNION(t))
            tstr = "union ";
    tstruct:
        pstrcat(buf, buf_size, tstr);
        v = type->ref->v & ~SYM_STRUCT;
        if (v >= SYM_FIRST_ANOM)
            pstrcat(buf, buf_size, "<anonymous>");
        else
            pstrcat(buf, buf_size, get_tok_str(v, NULL));
        break;
    case VT_FUNC:
        s = type->ref;
        type_to_str(buf, buf_size, &s->type, varstr);
        pstrcat(buf, buf_size, "(");
        sa = s->next;
        while (sa != NULL) {
            type_to_str(buf1, sizeof(buf1), &sa->type, NULL);
            pstrcat(buf, buf_size, buf1);
            sa = sa->next;
            if (sa)
                pstrcat(buf, buf_size, ", ");
        }
        pstrcat(buf, buf_size, ")");
        goto no_var;
    case VT_PTR:
        s = type->ref;
        if (t & VT_ARRAY) {
            snprintf(buf1, sizeof(buf1), "%s[%d]", varstr ? varstr : "", s->c);
            type_to_str(buf, buf_size, &s->type, buf1);
            goto no_var;
        }
        pstrcpy(buf1, sizeof(buf1), "*");
        if (t & VT_CONSTANT)
            pstrcat(buf1, buf_size, "const ");
        if (t & VT_VOLATILE)
            pstrcat(buf1, buf_size, "volatile ");
        if (varstr)
            pstrcat(buf1, sizeof(buf1), varstr);
        type_to_str(buf, buf_size, &s->type, buf1);
        goto no_var;
    }
    if (varstr) {
        pstrcat(buf, buf_size, " ");
        pstrcat(buf, buf_size, varstr);
    }
 no_var: ;
}

/* verify type compatibility to store vtop in 'dt' type, and generate
   casts if needed. */
static void gen_assign_cast(CType *dt)
{
    CType *st, *type1, *type2;
    char buf1[256], buf2[256];
    int dbt, sbt;

    st = &vtop->type; /* source type */
    dbt = dt->t & VT_BTYPE;
    sbt = st->t & VT_BTYPE;
    if (sbt == VT_VOID || dbt == VT_VOID) {
	if (sbt == VT_VOID && dbt == VT_VOID)
	    ; /*
	      It is Ok if both are void
	      A test program:
	        void func1() {}
		void func2() {
		  return func1();
		}
	      gcc accepts this program
	      */
	else  tcc_error(-1, "cannot cast from/to void");
    }
    if( dt->t & VT_CONSTANT )  tcc_error(0, "assignment of read-only location");
    switch(dbt) {
    case VT_PTR:
        /* special cases for pointers */
        /* '0' can also be a pointer */
        if (is_null_pointer(vtop))
            goto type_ok;
        /* accept implicit pointer to integer cast with warning */
        if (is_integer_btype(sbt)) {
            tcc_error(0, "assignment makes pointer from integer without a cast");
            goto type_ok;
        }
        type1 = pointed_type(dt);
        /* a function is implicitly a function pointer */
        if (sbt == VT_FUNC) {
            if ((type1->t & VT_BTYPE) != VT_VOID &&
                !is_compatible_types(pointed_type(dt), st))
                tcc_error(0, "assignment from incompatible pointer type");
            goto type_ok;
        }
        if (sbt != VT_PTR)
            goto error;
        type2 = pointed_type(st);
        if ((type1->t & VT_BTYPE) == VT_VOID || 
            (type2->t & VT_BTYPE) == VT_VOID) {
            /* void * can match anything */
        } else {
            //printf("types %08x %08x\n", type1->t, type2->t);
            /* exact type match, except for qualifiers */
            if (!is_compatible_unqualified_types(type1, type2)) {
		/* Like GCC don't warn by default for merely changes
		   in pointer target signedness.  Do warn for different
		   base types, though, in particular for unsigned enums
		   and signed int targets.  */
		if ((type1->t & (VT_BTYPE|VT_LONG)) != (type2->t & (VT_BTYPE|VT_LONG))
                    || IS_ENUM(type1->t) || IS_ENUM(type2->t)
                    )
		    tcc_error(0, "assignment from incompatible pointer type");
	    }
        }
        /* check const and volatile */
        if ((!(type1->t & VT_CONSTANT) && (type2->t & VT_CONSTANT)) ||
            (!(type1->t & VT_VOLATILE) && (type2->t & VT_VOLATILE)))
            tcc_error(0, "assignment discards qualifiers from pointer target type");
        break;
    case VT_BYTE:
    case VT_SHORT:
    case VT_INT:
    case VT_LLONG:
        if (sbt == VT_PTR || sbt == VT_FUNC) {
            tcc_error(0, "assignment makes integer from pointer without a cast");
        } else if (sbt == VT_STRUCT) {
            goto case_VT_STRUCT;
        }
        /* XXX: more tests */
        break;
    case VT_STRUCT:
    case_VT_STRUCT:
        if (!is_compatible_unqualified_types(dt, st)) {
        error:
            type_to_str(buf1, sizeof(buf1), st, NULL);
            type_to_str(buf2, sizeof(buf2), dt, NULL);
            tcc_error(-1, "cannot cast '%s' to '%s'", buf1, buf2);
        }
        break;
    }
 type_ok:
    gen_cast(dt);
}

/* store vtop in lvalue pushed on stack */
ST_FUNC void vstore(void)
{
    int sbt, dbt, ft, r, t, size, align, bit_size, bit_pos, rc, delayed_cast;

    ft = vtop[-1].type.t;
    sbt = vtop->type.t & VT_BTYPE;
    dbt = ft & VT_BTYPE;
    if ((((sbt == VT_INT || sbt == VT_SHORT) && dbt == VT_BYTE) ||
         (sbt == VT_INT && dbt == VT_SHORT))
	&& !(vtop->type.t & VT_BITFIELD)) {
        /* optimize char/short casts */
        delayed_cast = VT_MUSTCAST;
        vtop->type.t = ft & VT_TYPE;
        /* XXX: factorize */
        if( ft & VT_CONSTANT )  tcc_error(0, "assignment of read-only location");
    }
    else {
        delayed_cast = 0;
        if (!(ft & VT_BITFIELD))
            gen_assign_cast(&vtop[-1].type);
    }

    if (sbt == VT_STRUCT) {
        /* if structure, only generate pointer */
        /* structure assignment : generate memcpy */
        /* XXX: optimize if small size */
            size = type_size(&vtop->type, &align);

            /* destination */
            vswap();
            vtop->type.t = VT_PTR;
            gaddrof();

            /* address of memcpy() */
#ifdef TCC_ARM_EABI
            if(!(align & 7))
                vpush_global_sym(&func_old_type, TOK_memcpy8);
            else if(!(align & 3))
                vpush_global_sym(&func_old_type, TOK_memcpy4);
            else
#endif
            /* Use memmove, rather than memcpy, as dest and src may be same: */
            vpush_global_sym(&func_old_type, TOK_memmove);

            vswap();
            /* source */
            vpushv(vtop - 2);
            vtop->type.t = VT_PTR;
            gaddrof();
            /* type size */
            vpushi(size);
            gfunc_call(3);

        /* leave source on stack */
    } else if (ft & VT_BITFIELD) {
        /* bitfield store handling */

        /* save lvalue as expression result (example: s.b = s.a = n;) */
        vdup(), vtop[-1] = vtop[-2];

        bit_pos = BIT_POS(ft);
        bit_size = BIT_SIZE(ft);
        /* remove bit field info to avoid loops */
        vtop[-1].type.t = ft & ~VT_STRUCT_MASK;

        if ((ft & VT_BTYPE) == VT_BOOL) {
            gen_cast(&vtop[-1].type);
            vtop[-1].type.t = (vtop[-1].type.t & ~VT_BTYPE) | (VT_BYTE | VT_UNSIGNED);
        }

        r = adjust_bf(vtop - 1, bit_pos, bit_size);
        if (r == VT_STRUCT) {
            gen_cast_s((ft & VT_BTYPE) == VT_LLONG ? VT_LLONG : VT_INT);
            store_packed_bf(bit_pos, bit_size);
        } else {
            unsigned long long mask = (1ULL << bit_size) - 1;
            if ((ft & VT_BTYPE) != VT_BOOL) {
                /* mask source */
                if ((vtop[-1].type.t & VT_BTYPE) == VT_LLONG)
                    vpushll(mask);
                else
                    vpushi((unsigned)mask);
                gen_op('&');
            }
            /* shift source */
            vpushi(bit_pos);
            gen_op(TOK_SHL);
            vswap();
            /* duplicate destination */
            vdup();
            vrott(3);
            /* load destination, mask and or with source */
            if ((vtop->type.t & VT_BTYPE) == VT_LLONG)
                vpushll(~(mask << bit_pos));
            else
                vpushi(~((unsigned)mask << bit_pos));
            gen_op('&');
            gen_op('|');
            /* store result */
            vstore();
            /* ... and discard */
            vpop();
        }
    } else if (dbt == VT_VOID) {
        --vtop;
    } else {
#ifdef CONFIG_TCC_BCHECK
            /* bound check case */
            if (vtop[-1].r & VT_MUSTBOUND) {
                vswap();
                gbound();
                vswap();
            }
#endif
            rc = RC_INT;
            if (is_float(ft)) {
                rc = RC_FLOAT;
#ifdef TCC_TARGET_X86_64
                if ((ft & VT_BTYPE) == VT_LDOUBLE) {
                    rc = RC_ST0;
                } else if ((ft & VT_BTYPE) == VT_QFLOAT) {
                    rc = RC_FRET;
                }
#endif
            }
            r = gv(rc);  /* generate value */
            /* if lvalue was saved on stack, must read it */
            if ((vtop[-1].r & VT_VALMASK) == VT_LLOCAL) {
                SValue sv;
                t = get_reg(RC_INT);
#if PTR_SIZE == 8
                sv.type.t = VT_PTR;
#else
                sv.type.t = VT_INT;
#endif
                sv.r = VT_LOCAL | VT_LVAL;
                sv.c.i = vtop[-1].c.i;
                load(t, &sv);
                vtop[-1].r = t | VT_LVAL;
            }
            /* two word case handling : store second register at word + 4 (or +8 for x86-64)  */
#if PTR_SIZE == 8
            if (((ft & VT_BTYPE) == VT_QLONG) || ((ft & VT_BTYPE) == VT_QFLOAT)) {
                int addr_type = VT_LLONG, load_size = 8, load_type = ((vtop->type.t & VT_BTYPE) == VT_QLONG) ? VT_LLONG : VT_DOUBLE;
#else
            if ((ft & VT_BTYPE) == VT_LLONG) {
                int addr_type = VT_INT, load_size = 4, load_type = VT_INT;
#endif
                vtop[-1].type.t = load_type;
                store(r, vtop - 1);
                vswap();
                /* convert to int to increment easily */
                vtop->type.t = addr_type;
                gaddrof();
                vpushi(load_size);
                gen_op('+');
                vtop->r |= VT_LVAL;
                vswap();
                vtop[-1].type.t = load_type;
                /* XXX: it works because r2 is spilled last ! */
                store(vtop->r2, vtop - 1);
            } else {
                store(r, vtop - 1);
            }

        vswap();
        vtop--; /* NOT vpop() because on x86 it would flush the fp stack */
        vtop->r |= delayed_cast;
    }
}

/* post defines POST/PRE add. c is the token ++ or -- */
ST_FUNC void inc(int post, int c)
{
    test_lvalue();
    vdup(); /* save lvalue */
    if (post) {
        gv_dup(); /* duplicate value */
        vrotb(3);
        vrotb(3);
    }
    /* add constant */
    vpushi(c - TOK_MID); 
    gen_op('+');
    vstore(); /* store value */
    if (post)
        vpop(); /* if post op, return saved value */
}

ST_FUNC void parse_mult_str (CString *astr, const char *msg)
{
    /* read the string */
    if( tok != TOK_STR )  tcc_error(-1, "%s expected", msg );
    cstr_new(astr);
    while (tok == TOK_STR) {
        /* XXX: add \0 handling too ? */
        cstr_cat(astr, tokc.str.data, -1);
        next();
    }
    cstr_ccat(astr, '\0');
}

/* If I is >= 1 and a power of two, returns log2(i)+1.
   If I is 0 returns 0.  */
static int exact_log2p1(int i)
{
  int ret;
  if (!i)
    return 0;
  for (ret = 1; i >= 1 << 8; ret += 8)
    i >>= 8;
  if (i >= 1 << 4)
    ret += 4, i >>= 4;
  if (i >= 1 << 2)
    ret += 2, i >>= 2;
  if (i >= 1 << 1)
    ret++;
  return ret;
}

/* Parse __attribute__((...)) GNUC extension. */
static void parse_attribute(AttributeDef *ad)
{
    int t, n;
    CString astr;
    
redo:
    if (tok != TOK_ATTRIBUTE1 && tok != TOK_ATTRIBUTE2)
        return;
    next();
    skip('(');
    skip('(');
    while (tok != ')') {
        if( tok < TOK_IDENT )  tcc_error(-1, "attribute name expected" );
        t = tok;
        next();
        switch(t) {
        case TOK_SECTION1:
        case TOK_SECTION2:
            skip('(');
	    parse_mult_str(&astr, "section name");
            ad->section = find_section(tcc_state, (char *)astr.data);
            skip(')');
	    cstr_free(&astr);
            break;
        case TOK_ALIAS1:
        case TOK_ALIAS2:
            skip('(');
	    parse_mult_str(&astr, "alias(\"target\")");
            ad->alias_target = /* save string as token, for later */
              tok_alloc((char*)astr.data, astr.size-1)->tok;
            skip(')');
	    cstr_free(&astr);
            break;
	case TOK_VISIBILITY1:
	case TOK_VISIBILITY2:
            skip('(');
	    parse_mult_str(&astr,
			   "visibility(\"default|hidden|internal|protected\")");
	    if (!strcmp (astr.data, "default"))
	        ad->a.visibility = STV_DEFAULT;
	    else if (!strcmp (astr.data, "hidden"))
	        ad->a.visibility = STV_HIDDEN;
	    else if (!strcmp (astr.data, "internal"))
	        ad->a.visibility = STV_INTERNAL;
	    else if (!strcmp (astr.data, "protected"))
	        ad->a.visibility = STV_PROTECTED;
	    else  tcc_error(-1, "visibility(\"default|hidden|internal|protected\") expected" );
            skip(')');
	    cstr_free(&astr);
            break;
        case TOK_ALIGNED1:
        case TOK_ALIGNED2:
            if (tok == '(') {
                next();
                n = expr_const();
                if (n <= 0 || (n & (n - 1)) != 0) 
                    tcc_error(-1, "alignment must be a positive power of two");
                skip(')');
            } else {
                n = MAX_ALIGN;
            }
            ad->a.aligned = exact_log2p1(n);
	    if (n != 1 << (ad->a.aligned - 1))
	      tcc_error(-1, "alignment of %d is larger than implemented", n);
            break;
        case TOK_PACKED1:
        case TOK_PACKED2:
            ad->a.packed = 1;
            break;
        case TOK_WEAK1:
        case TOK_WEAK2:
            ad->a.weak = 1;
            break;
        case TOK_UNUSED1:
        case TOK_UNUSED2:
            /* currently, no need to handle it because tcc does not
               track unused objects */
            break;
        case TOK_NORETURN1:
        case TOK_NORETURN2:
            /* currently, no need to handle it because tcc does not
               track unused objects */
            break;
        case TOK_CDECL1:
        case TOK_CDECL2:
        case TOK_CDECL3:
            ad->f.func_call = FUNC_CDECL;
            break;
        case TOK_STDCALL1:
        case TOK_STDCALL2:
        case TOK_STDCALL3:
            ad->f.func_call = FUNC_STDCALL;
            break;
#ifdef TCC_TARGET_I386
        case TOK_REGPARM1:
        case TOK_REGPARM2:
            skip('(');
            n = expr_const();
            if (n > 3) 
                n = 3;
            else if (n < 0)
                n = 0;
            if (n > 0)
                ad->f.func_call = FUNC_FASTCALL1 + n - 1;
            skip(')');
            break;
        case TOK_FASTCALL1:
        case TOK_FASTCALL2:
        case TOK_FASTCALL3:
            ad->f.func_call = FUNC_FASTCALLW;
            break;            
#endif
        case TOK_MODE:
            skip('(');
            switch(tok) {
                case TOK_MODE_DI:
                    ad->attr_mode = VT_LLONG + 1;
                    break;
                case TOK_MODE_QI:
                    ad->attr_mode = VT_BYTE + 1;
                    break;
                case TOK_MODE_HI:
                    ad->attr_mode = VT_SHORT + 1;
                    break;
                case TOK_MODE_SI:
                case TOK_MODE_word:
                    ad->attr_mode = VT_INT + 1;
                    break;
                default:
                    tcc_error(0, "__mode__(%s) not supported\n", get_tok_str(tok, NULL));
                    break;
            }
            next();
            skip(')');
            break;
        case TOK_DLLEXPORT:
            ad->a.dllexport = 1;
            break;
        case TOK_DLLIMPORT:
            ad->a.dllimport = 1;
            break;
        default:
            if (tcc_state->warn_unsupported)
                tcc_error(0, "'%s' attribute ignored", get_tok_str(t, NULL));
            /* skip parameters */
            if (tok == '(') {
                int parenthesis = 0;
                do {
                    if (tok == '(') 
                        parenthesis++;
                    else if (tok == ')') 
                        parenthesis--;
                    next();
                } while (parenthesis && tok != -1);
            }
            break;
        }
        if (tok != ',')
            break;
        next();
    }
    skip(')');
    skip(')');
    goto redo;
}

static Sym * find_field (CType *type, int v)
{
    Sym *s = type->ref;
    v |= SYM_FIELD;
    while ((s = s->next) != NULL) {
	if ((s->v & SYM_FIELD) &&
	    (s->type.t & VT_BTYPE) == VT_STRUCT &&
	    (s->v & ~SYM_FIELD) >= SYM_FIRST_ANOM) {
	    Sym *ret = find_field (&s->type, v);
	    if (ret)
	        return ret;
	}
	if (s->v == v)
	  break;
    }
    return s;
}

static void struct_add_offset (Sym *s, int offset)
{
    while ((s = s->next) != NULL) {
	if ((s->v & SYM_FIELD) &&
	    (s->type.t & VT_BTYPE) == VT_STRUCT &&
	    (s->v & ~SYM_FIELD) >= SYM_FIRST_ANOM) {
	    struct_add_offset(s->type.ref, offset);
	} else
	  s->c += offset;
    }
}

static void struct_layout(CType *type, AttributeDef *ad)
{
    int size, align, maxalign, offset, c, bit_pos, bit_size;
    int packed, a, bt, prevbt, prev_bit_size;
    int pcc = !tcc_state->ms_bitfields;
    int pragma_pack = *tcc_state->pack_stack_ptr;
    Sym *f;

    maxalign = 1;
    offset = 0;
    c = 0;
    bit_pos = 0;
    prevbt = VT_STRUCT; /* make it never match */
    prev_bit_size = 0;

//#define BF_DEBUG

    for (f = type->ref->next; f; f = f->next) {
        if (f->type.t & VT_BITFIELD)
            bit_size = BIT_SIZE(f->type.t);
        else
            bit_size = -1;
        size = type_size(&f->type, &align);
        a = f->a.aligned ? 1 << (f->a.aligned - 1) : 0;
        packed = 0;

        if (pcc && bit_size == 0) {
            /* in pcc mode, packing does not affect zero-width bitfields */

        } else {
            /* in pcc mode, attribute packed overrides if set. */
            if (pcc && (f->a.packed || ad->a.packed))
                align = packed = 1;

            /* pragma pack overrides align if lesser and packs bitfields always */
            if (pragma_pack) {
                packed = 1;
                if (pragma_pack < align)
                    align = pragma_pack;
                /* in pcc mode pragma pack also overrides individual align */
                if (pcc && pragma_pack < a)
                    a = 0;
            }
        }
        /* some individual align was specified */
        if (a)
            align = a;

        if (type->ref->type.t == VT_UNION) {
	    if (pcc && bit_size >= 0)
	        size = (bit_size + 7) >> 3;
	    offset = 0;
	    if (size > c)
	        c = size;

	} else if (bit_size < 0) {
            if (pcc)
                c += (bit_pos + 7) >> 3;
	    c = (c + align - 1) & -align;
	    offset = c;
	    if (size > 0)
	        c += size;
	    bit_pos = 0;
	    prevbt = VT_STRUCT;
	    prev_bit_size = 0;

	} else {
	    /* A bit-field.  Layout is more complicated.  There are two
	       options: PCC (GCC) compatible and MS compatible */
            if (pcc) {
		/* In PCC layout a bit-field is placed adjacent to the
                   preceding bit-fields, except if:
                   - it has zero-width
                   - an individual alignment was given
                   - it would overflow its base type container and
                     there is no packing */
                if (bit_size == 0) {
            new_field:
		    c = (c + ((bit_pos + 7) >> 3) + align - 1) & -align;
		    bit_pos = 0;
                } else if (f->a.aligned) {
                    goto new_field;
                } else if (!packed) {
                    int a8 = align * 8;
	            int ofs = ((c * 8 + bit_pos) % a8 + bit_size + a8 - 1) / a8;
                    if (ofs > size / align)
                        goto new_field;
                }

                /* in pcc mode, long long bitfields have type int if they fit */
                if (size == 8 && bit_size <= 32)
                    f->type.t = (f->type.t & ~VT_BTYPE) | VT_INT, size = 4;

                while (bit_pos >= align * 8)
                    c += align, bit_pos -= align * 8;
                offset = c;

		/* In PCC layout named bit-fields influence the alignment
		   of the containing struct using the base types alignment,
		   except for packed fields (which here have correct align).  */
		if (f->v & SYM_FIRST_ANOM
                    // && bit_size // ??? gcc on ARM/rpi does that
                    )
		    align = 1;

	    } else {
		bt = f->type.t & VT_BTYPE;
		if ((bit_pos + bit_size > size * 8)
                    || (bit_size > 0) == (bt != prevbt)
                    ) {
		    c = (c + align - 1) & -align;
		    offset = c;
		    bit_pos = 0;
		    /* In MS bitfield mode a bit-field run always uses
		       at least as many bits as the underlying type.
		       To start a new run it's also required that this
		       or the last bit-field had non-zero width.  */
		    if (bit_size || prev_bit_size)
		        c += size;
		}
		/* In MS layout the records alignment is normally
		   influenced by the field, except for a zero-width
		   field at the start of a run (but by further zero-width
		   fields it is again).  */
		if (bit_size == 0 && prevbt != bt)
		    align = 1;
		prevbt = bt;
                prev_bit_size = bit_size;
	    }

	    f->type.t = (f->type.t & ~(0x3f << VT_STRUCT_SHIFT))
		        | (bit_pos << VT_STRUCT_SHIFT);
	    bit_pos += bit_size;
	}
	if (align > maxalign)
	    maxalign = align;

#ifdef BF_DEBUG
	printf("set field %s offset %-2d size %-2d align %-2d",
	       get_tok_str(f->v & ~SYM_FIELD, NULL), offset, size, align);
	if (f->type.t & VT_BITFIELD) {
	    printf(" pos %-2d bits %-2d",
                    BIT_POS(f->type.t),
                    BIT_SIZE(f->type.t)
                    );
	}
	printf("\n");
#endif

	if (f->v & SYM_FIRST_ANOM && (f->type.t & VT_BTYPE) == VT_STRUCT) {
	    Sym *ass;
	    /* An anonymous struct/union.  Adjust member offsets
	       to reflect the real offset of our containing struct.
	       Also set the offset of this anon member inside
	       the outer struct to be zero.  Via this it
	       works when accessing the field offset directly
	       (from base object), as well as when recursing
	       members in initializer handling.  */
	    int v2 = f->type.ref->v;
	    if (!(v2 & SYM_FIELD) &&
		(v2 & ~SYM_STRUCT) < SYM_FIRST_ANOM) {
		Sym **pps;
		/* This happens only with MS extensions.  The
		   anon member has a named struct type, so it
		   potentially is shared with other references.
		   We need to unshare members so we can modify
		   them.  */
		ass = f->type.ref;
		f->type.ref = sym_push(anon_sym++ | SYM_FIELD,
				       &f->type.ref->type, 0,
				       f->type.ref->c);
		pps = &f->type.ref->next;
		while ((ass = ass->next) != NULL) {
		    *pps = sym_push(ass->v, &ass->type, 0, ass->c);
		    pps = &((*pps)->next);
		}
		*pps = NULL;
	    }
	    struct_add_offset(f->type.ref, offset);
	    f->c = 0;
	} else {
	    f->c = offset;
	}

	f->r = 0;
    }

    if (pcc)
        c += (bit_pos + 7) >> 3;

    /* store size and alignment */
    a = bt = ad->a.aligned ? 1 << (ad->a.aligned - 1) : 1;
    if (a < maxalign)
        a = maxalign;
    type->ref->r = a;
    if (pragma_pack && pragma_pack < maxalign && 0 == pcc) {
        /* can happen if individual align for some member was given.  In
           this case MSVC ignores maxalign when aligning the size */
        a = pragma_pack;
        if (a < bt)
            a = bt;
    }
    c = (c + a - 1) & -a;
    type->ref->c = c;

#ifdef BF_DEBUG
    printf("struct size %-2d align %-2d\n\n", c, a), fflush(stdout);
#endif

    /* check whether we can access bitfields by their type */
    for (f = type->ref->next; f; f = f->next) {
        int s, px, cx, c0;
        CType t;

        if (0 == (f->type.t & VT_BITFIELD))
            continue;
        f->type.ref = f;
        f->auxtype = -1;
        bit_size = BIT_SIZE(f->type.t);
        if (bit_size == 0)
            continue;
        bit_pos = BIT_POS(f->type.t);
        size = type_size(&f->type, &align);
        if (bit_pos + bit_size <= size * 8 && f->c + size <= c)
            continue;

        /* try to access the field using a different type */
        c0 = -1, s = align = 1;
        for (;;) {
            px = f->c * 8 + bit_pos;
            cx = (px >> 3) & -align;
            px = px - (cx << 3);
            if (c0 == cx)
                break;
            s = (px + bit_size + 7) >> 3;
            if (s > 4) {
                t.t = VT_LLONG;
            } else if (s > 2) {
                t.t = VT_INT;
            } else if (s > 1) {
                t.t = VT_SHORT;
            } else {
                t.t = VT_BYTE;
            }
            s = type_size(&t, &align);
            c0 = cx;
        }

        if (px + bit_size <= s * 8 && cx + s <= c) {
            /* update offset and bit position */
            f->c = cx;
            bit_pos = px;
	    f->type.t = (f->type.t & ~(0x3f << VT_STRUCT_SHIFT))
		        | (bit_pos << VT_STRUCT_SHIFT);
            if (s != size)
                f->auxtype = t.t;
#ifdef BF_DEBUG
            printf("FIX field %s offset %-2d size %-2d align %-2d "
                "pos %-2d bits %-2d\n",
                get_tok_str(f->v & ~SYM_FIELD, NULL),
                cx, s, align, px, bit_size);
#endif
        } else {
            /* fall back to load/store single-byte wise */
            f->auxtype = VT_STRUCT;
#ifdef BF_DEBUG
            printf("FIX field %s : load byte-wise\n",
                 get_tok_str(f->v & ~SYM_FIELD, NULL));
#endif
        }
    }
}

/* enum/struct/union declaration. u is VT_ENUM/VT_STRUCT/VT_UNION */
static void struct_decl(CType *type, int u)
{
    int v, c, size, align, flexible;
    int bit_size, bsize, bt;
    Sym *s, *ss, **ps;
    AttributeDef ad, ad1;
    CType type1, btype;

    memset(&ad, 0, sizeof ad);
    next();
    parse_attribute(&ad);
    if (tok != '{') {
        v = tok;
        next();
        /* struct already defined ? return it */
        if( v < TOK_IDENT )  tcc_error(-1, "struct/union/enum name expected" );
        s = struct_find(v);
        if (s && (s->sym_scope == local_scope || tok != '{')) {
            if (u == s->type.t)
                goto do_decl;
            if (u == VT_ENUM && IS_ENUM(s->type.t))
                goto do_decl;
            tcc_error(-1, "redefinition of '%s'", get_tok_str(v, NULL));
        }
    } else {
        v = anon_sym++;
    }
    /* Record the original enum/struct/union token.  */
    type1.t = u == VT_ENUM ? u | VT_INT | VT_UNSIGNED : u;
    type1.ref = NULL;
    /* we put an undefined size for struct/union */
    s = sym_push(v | SYM_STRUCT, &type1, 0, -1);
    s->r = 0; /* default alignment is zero as gcc */
do_decl:
    type->t = s->type.t;
    type->ref = s;

    if (tok == '{') {
        next();
        if( s->c != -1 )  tcc_error(-1, "struct/union/enum already defined");
        /* cannot be empty */
        /* non empty enums are not allowed */
        ps = &s->next;
        if (u == VT_ENUM) {
            long long ll = 0, pl = 0, nl = 0;
	    CType t;
            t.ref = s;
            /* enum symbols have static storage */
            t.t = VT_INT|VT_STATIC|VT_ENUM_VAL;
            for(;;) {
                v = tok;
                if( v < TOK_UIDENT )  tcc_error(-1, "identifier expected" );
                ss = sym_find(v);
                if( ss && !local_stack )  tcc_error(-1, "redefinition of enumerator '%s'", get_tok_str(v, NULL));
                next();
                if (tok == '=') {
                    next();
		    ll = expr_const64();
                }
                ss = sym_push(v, &t, VT_CONST, 0);
                ss->enum_val = ll;
                *ps = ss, ps = &ss->next;
                if (ll < nl)
                    nl = ll;
                if (ll > pl)
                    pl = ll;
                if (tok != ',')
                    break;
                next();
                ll++;
                /* NOTE: we accept a trailing comma */
                if (tok == '}')
                    break;
            }
            skip('}');
            /* set integral type of the enum */
            t.t = VT_INT;
            if (nl >= 0) {
                if (pl != (unsigned)pl)
                    t.t = (LONG_SIZE==8 ? VT_LLONG|VT_LONG : VT_LLONG);
                t.t |= VT_UNSIGNED;
            } else if (pl != (int)pl || nl != (int)nl)
                t.t = (LONG_SIZE==8 ? VT_LLONG|VT_LONG : VT_LLONG);
            s->type.t = type->t = t.t | VT_ENUM;
            s->c = 0;
            /* set type for enum members */
            for (ss = s->next; ss; ss = ss->next) {
                ll = ss->enum_val;
                if (ll == (int)ll) /* default is int if it fits */
                    continue;
                if (t.t & VT_UNSIGNED) {
                    ss->type.t |= VT_UNSIGNED;
                    if (ll == (unsigned)ll)
                        continue;
                }
                ss->type.t = (ss->type.t & ~VT_BTYPE)
                    | (LONG_SIZE==8 ? VT_LLONG|VT_LONG : VT_LLONG);
            }
        } else {
            c = 0;
            flexible = 0;
            while (tok != '}') {
                if (!parse_btype(&btype, &ad1)) {
		    skip(';');
		    continue;
		}
                while( 1 ) {
		    if( flexible )
		        tcc_error(-1, "flexible array member '%s' not at the end of struct", get_tok_str(v, NULL));
                    bit_size = -1;
                    v = 0;
                    type1 = btype;
                    if (tok != ':') {
			if (tok != ';')
                            type_decl(&type1, &ad1, &v, TYPE_DIRECT);
                        if( v == 0 ) {
                    	    if(( type1.t & VT_BTYPE) != VT_STRUCT )  tcc_error(-1, "identifier expected" );
                    	    else {
				int v = btype.ref->v;
				if (!(v & SYM_FIELD) && (v & ~SYM_STRUCT) < SYM_FIRST_ANOM) {
				    if( 0 == tcc_state->ms_extensions )  tcc_error(-1, "identifier expected" );
				}
                    	    }
                        }
                        if (type_size(&type1, &align) < 0) {
			    if(( u == VT_STRUCT ) && ( type1.t & VT_ARRAY ) && c )  flexible = 1;
			    else  tcc_error(-1, "field '%s' has incomplete type", get_tok_str(v, NULL));
                        }
                        if(( type1.t & VT_BTYPE) == VT_FUNC || (type1.t & VT_STORAGE))
                            tcc_error(-1, "invalid type for '%s'", get_tok_str(v, NULL));
                    }
                    if (tok == ':') {
                        next();
                        bit_size = expr_const();
                        /* XXX: handle v = 0 case for messages */
                        if( bit_size < 0 )  tcc_error(-1, "negative width in bit-field '%s'", get_tok_str(v, NULL));
                        if( v && bit_size == 0 )  tcc_error(-1, "zero width for bit-field '%s'", get_tok_str(v, NULL));
			parse_attribute(&ad1);
                    }
                    size = type_size(&type1, &align);
                    if (bit_size >= 0) {
                        bt = type1.t & VT_BTYPE;
                        if (bt != VT_INT && 
                            bt != VT_BYTE && 
                            bt != VT_SHORT &&
                            bt != VT_BOOL &&
                            bt != VT_LLONG)
                            tcc_error(-1, "bitfields must have scalar type");
                        bsize = size * 8;
                        if (bit_size > bsize) {
                            tcc_error(-1, "width of '%s' exceeds its type",
                                  get_tok_str(v, NULL));
                        } else if (bit_size == bsize
                                    && !ad.a.packed && !ad1.a.packed) {
                            /* no need for bit fields */
                            ;
                        } else if (bit_size == 64) {
                            tcc_error(-1, "field width 64 not implemented");
                        } else {
                            type1.t = (type1.t & ~VT_STRUCT_MASK)
                                | VT_BITFIELD
                                | (bit_size << (VT_STRUCT_SHIFT + 6));
                        }
                    }
                    if (v != 0 || (type1.t & VT_BTYPE) == VT_STRUCT) {
                        /* Remember we've seen a real field to check
			   for placement of flexible array member. */
			c = 1;
                    }
		    /* If member is a struct or bit-field, enforce
		       placing into the struct (as anonymous).  */
                    if (v == 0 &&
			((type1.t & VT_BTYPE) == VT_STRUCT ||
			 bit_size >= 0)) {
		        v = anon_sym++;
		    }
                    if (v) {
                        ss = sym_push(v | SYM_FIELD, &type1, 0, 0);
                        ss->a = ad1.a;
                        *ps = ss;
                        ps = &ss->next;
                    }
                    if (tok == ';' || tok == TOK_EOF)
                        break;
                    skip(',');
                }
                skip(';');
            }
            skip('}');
	    parse_attribute(&ad);
	    struct_layout(type, &ad);
        }
    }
}

static void sym_to_attr(AttributeDef *ad, Sym *s)
{
    if (s->a.aligned && 0 == ad->a.aligned)
        ad->a.aligned = s->a.aligned;
    if (s->f.func_call && 0 == ad->f.func_call)
        ad->f.func_call = s->f.func_call;
    if (s->f.func_type && 0 == ad->f.func_type)
        ad->f.func_type = s->f.func_type;
    if (s->a.packed)
        ad->a.packed = 1;
}

/* Add type qualifiers to a type. If the type is an array then the qualifiers
   are added to the element type, copied because it could be a typedef. */
static void parse_btype_qualify(CType *type, int qualifiers)
{
    while (type->t & VT_ARRAY) {
        type->ref = sym_push(SYM_FIELD, &type->ref->type, 0, type->ref->c);
        type = &type->ref->type;
    }
    type->t |= qualifiers;
}

/* return 0 if no type declaration. otherwise, return the basic type
   and skip it. 
 */
static int parse_btype(CType *type, AttributeDef *ad)
{
    int t, u, bt, st, type_found, typespec_found, g;
    Sym *s;
    CType type1;

    memset(ad, 0, sizeof(AttributeDef));
    type_found = 0;
    typespec_found = 0;
    t = VT_INT;
    bt = st = -1;
    type->ref = NULL;

    while(1) {
        switch(tok) {
        case TOK_EXTENSION:
            /* currently, we really ignore extension */
            next();
            continue;

            /* basic types */
        case TOK_CHAR:
            u = VT_BYTE;
        basic_type:
            next();
        basic_type1:
            if (u == VT_SHORT || u == VT_LONG) {
                if (st != -1 || (bt != -1 && bt != VT_INT))
                    tmbt: tcc_error(-1, "too many basic types");
                st = u;
            } else {
                if (bt != -1 || (st != -1 && u != VT_INT))
                    goto tmbt;
                bt = u;
            }
            if (u != VT_INT)
                t = (t & ~(VT_BTYPE|VT_LONG)) | u;
            typespec_found = 1;
            break;
        case TOK_VOID:
            u = VT_VOID;
            goto basic_type;
        case TOK_SHORT:
            u = VT_SHORT;
            goto basic_type;
        case TOK_INT:
            u = VT_INT;
            goto basic_type;
        case TOK_LONG:
            if ((t & VT_BTYPE) == VT_DOUBLE) {
                t = (t & ~(VT_BTYPE|VT_LONG)) | VT_LDOUBLE;
            } else if ((t & (VT_BTYPE|VT_LONG)) == VT_LONG) {
                t = (t & ~(VT_BTYPE|VT_LONG)) | VT_LLONG;
            } else {
                u = VT_LONG;
                goto basic_type;
            }
            next();
            break;
#ifdef TCC_TARGET_ARM64
        case TOK_UINT128:
            /* GCC's __uint128_t appears in some Linux header files. Make it a
               synonym for long double to get the size and alignment right. */
            u = VT_LDOUBLE;
            goto basic_type;
#endif
        case TOK_BOOL:
            u = VT_BOOL;
            goto basic_type;
        case TOK_FLOAT:
            u = VT_FLOAT;
            goto basic_type;
        case TOK_DOUBLE:
            if ((t & (VT_BTYPE|VT_LONG)) == VT_LONG) {
                t = (t & ~(VT_BTYPE|VT_LONG)) | VT_LDOUBLE;
            } else {
                u = VT_DOUBLE;
                goto basic_type;
            }
            next();
            break;
        case TOK_ENUM:
            struct_decl(&type1, VT_ENUM);
        basic_type2:
            u = type1.t;
            type->ref = type1.ref;
            goto basic_type1;
        case TOK_STRUCT:
            struct_decl(&type1, VT_STRUCT);
            goto basic_type2;
        case TOK_UNION:
            struct_decl(&type1, VT_UNION);
            goto basic_type2;

            /* type modifiers */
        case TOK_CONST1:
        case TOK_CONST2:
        case TOK_CONST3:
            type->t = t;
            parse_btype_qualify(type, VT_CONSTANT);
            t = type->t;
            next();
            break;
        case TOK_VOLATILE1:
        case TOK_VOLATILE2:
        case TOK_VOLATILE3:
            type->t = t;
            parse_btype_qualify(type, VT_VOLATILE);
            t = type->t;
            next();
            break;
        case TOK_SIGNED1:
        case TOK_SIGNED2:
        case TOK_SIGNED3:
            if ((t & (VT_DEFSIGN|VT_UNSIGNED)) == (VT_DEFSIGN|VT_UNSIGNED))
                tcc_error(-1, "signed and unsigned modifier");
            t |= VT_DEFSIGN;
            next();
            typespec_found = 1;
            break;
        case TOK_REGISTER:
        case TOK_AUTO:
        case TOK_RESTRICT1:
        case TOK_RESTRICT2:
        case TOK_RESTRICT3:
            next();
            break;
        case TOK_UNSIGNED:
            if ((t & (VT_DEFSIGN|VT_UNSIGNED)) == VT_DEFSIGN)
                tcc_error(-1, "signed and unsigned modifier");
            t |= VT_DEFSIGN | VT_UNSIGNED;
            next();
            typespec_found = 1;
            break;

            /* storage */
        case TOK_EXTERN:
            g = VT_EXTERN;
            goto storage;
        case TOK_STATIC:
            g = VT_STATIC;
            goto storage;
        case TOK_TYPEDEF:
            g = VT_TYPEDEF;
            goto storage;
       storage:
            if (t & (VT_EXTERN|VT_STATIC|VT_TYPEDEF) & ~g)
                tcc_error(-1, "multiple storage classes");
            t |= g;
            next();
            break;
        case TOK_INLINE1:
        case TOK_INLINE2:
        case TOK_INLINE3:
            t |= VT_INLINE;
            next();
            break;

            /* GNUC attribute */
        case TOK_ATTRIBUTE1:
        case TOK_ATTRIBUTE2:
            parse_attribute(ad);
            if (ad->attr_mode) {
                u = ad->attr_mode -1;
                t = (t & ~(VT_BTYPE|VT_LONG)) | u;
            }
            break;
            /* GNUC typeof */
        case TOK_TYPEOF1:
        case TOK_TYPEOF2:
        case TOK_TYPEOF3:
            next();
            parse_expr_type(&type1);
            /* remove all storage modifiers except typedef */
            type1.t &= ~(VT_STORAGE&~VT_TYPEDEF);
	    if (type1.ref)
                sym_to_attr(ad, type1.ref);
            goto basic_type2;
        default:
            if (typespec_found)
                goto the_end;
            s = sym_find(tok);
            if (!s || !(s->type.t & VT_TYPEDEF))
                goto the_end;
            t &= ~(VT_BTYPE|VT_LONG);
            u = t & ~(VT_CONSTANT | VT_VOLATILE), t ^= u;
            type->t = (s->type.t & ~VT_TYPEDEF) | u;
            type->ref = s->type.ref;
            if (t)
                parse_btype_qualify(type, t);
            t = type->t;
            /* get attributes from typedef */
            sym_to_attr(ad, s);
            next();
            typespec_found = 1;
            st = bt = -2;
            break;
        }
        type_found = 1;
    }
the_end:
    if (tcc_state->char_is_unsigned) {
        if ((t & (VT_DEFSIGN|VT_BTYPE)) == VT_BYTE)
            t |= VT_UNSIGNED;
    }
    /* VT_LONG is used just as a modifier for VT_INT / VT_LLONG */
    bt = t & (VT_BTYPE|VT_LONG);
    if (bt == VT_LONG)
        t |= LONG_SIZE == 8 ? VT_LLONG : VT_INT;
#ifdef TCC_TARGET_PE
    if (bt == VT_LDOUBLE)
        t = (t & ~(VT_BTYPE|VT_LONG)) | VT_DOUBLE;
#endif
    type->t = t;
    return type_found;
}

/* convert a function parameter type (array to pointer and function to
   function pointer) */
static inline void convert_parameter_type(CType *pt)
{
    /* remove const and volatile qualifiers (XXX: const could be used
       to indicate a const function parameter */
    pt->t &= ~(VT_CONSTANT | VT_VOLATILE);
    /* array must be transformed to pointer according to ANSI C */
    pt->t &= ~VT_ARRAY;
    if ((pt->t & VT_BTYPE) == VT_FUNC) {
        mk_pointer(pt);
    }
}

ST_FUNC void parse_asm_str(CString *astr)
{
    skip('(');
    parse_mult_str(astr, "string constant");
}

/* Parse an asm label and return the token */
static int asm_label_instr(void)
{
    int v;
    CString astr;

    next();
    parse_asm_str(&astr);
    skip(')');
#ifdef ASM_DEBUG
    printf("asm_alias: \"%s\"\n", (char *)astr.data);
#endif
    v = tok_alloc(astr.data, astr.size - 1)->tok;
    cstr_free(&astr);
    return v;
}

static int post_type(CType *type, AttributeDef *ad, int storage, int td)
{
    int n, l, t1, arg_size, align;
    Sym **plast, *s, *first;
    AttributeDef ad1;
    CType pt;

    if (tok == '(') {
        /* function type, or recursive declarator (return if so) */
        next();
	if (td && !(td & TYPE_ABSTRACT))
	  return 0;
	if (tok == ')')
	  l = 0;
	else if (parse_btype(&pt, &ad1))
	  l = FUNC_NEW;
	else if (td)
	  return 0;
	else
	  l = FUNC_OLD;
        first = NULL;
        plast = &first;
        arg_size = 0;
        if (l) {
            for(;;) {
                /* read param name and compute offset */
                if (l != FUNC_OLD) {
                    if ((pt.t & VT_BTYPE) == VT_VOID && tok == ')')
                        break;
                    type_decl(&pt, &ad1, &n, TYPE_DIRECT | TYPE_ABSTRACT);
                    if ((pt.t & VT_BTYPE) == VT_VOID)
                        tcc_error(-1, "parameter declared as void");
                    arg_size += (type_size(&pt, &align) + PTR_SIZE - 1) / PTR_SIZE;
                } else {
                    n = tok;
                    if( n < TOK_UIDENT )  tcc_error(-1, "identifier expected" );
                    pt.t = VT_VOID; /* invalid type */
                    next();
                }
                convert_parameter_type(&pt);
                s = sym_push(n | SYM_FIELD, &pt, 0, 0);
                *plast = s;
                plast = &s->next;
                if (tok == ')')
                    break;
                skip(',');
                if (l == FUNC_NEW && tok == TOK_DOTS) {
                    l = FUNC_ELLIPSIS;
                    next();
                    break;
                }
		if (l == FUNC_NEW && !parse_btype(&pt, &ad1))
		    tcc_error(-1, "invalid type");
            }
        } else
            /* if no parameters, then old type prototype */
            l = FUNC_OLD;
        skip(')');
        /* NOTE: const is ignored in returned type as it has a special
           meaning in gcc / C++ */
        type->t &= ~VT_CONSTANT; 
        /* some ancient pre-K&R C allows a function to return an array
           and the array brackets to be put after the arguments, such 
           that "int c()[]" means something like "int[] c()" */
        if (tok == '[') {
            next();
            skip(']'); /* only handle simple "[]" */
            mk_pointer(type);
        }
        /* we push a anonymous symbol which will contain the function prototype */
        ad->f.func_args = arg_size;
        ad->f.func_type = l;
        s = sym_push(SYM_FIELD, type, 0, 0);
        s->a = ad->a;
        s->f = ad->f;
        s->next = first;
        type->t = VT_FUNC;
        type->ref = s;
    } else if (tok == '[') {
	int saved_nocode_wanted = nocode_wanted;
        /* array definition */
        next();
        if (tok == TOK_RESTRICT1)
            next();
        n = -1;
        t1 = 0;
        if (tok != ']') {
            if (!local_stack || (storage & VT_STATIC))
                vpushi(expr_const());
            else {
		/* VLAs (which can only happen with local_stack && !VT_STATIC)
		   length must always be evaluated, even under nocode_wanted,
		   so that its size slot is initialized (e.g. under sizeof
		   or typeof).  */
		nocode_wanted = 0;
		gexpr();
	    }
            if ((vtop->r & (VT_VALMASK | VT_LVAL | VT_SYM)) == VT_CONST) {
                n = vtop->c.i;
                if (n < 0)
                    tcc_error(-1, "invalid array size");
            } else {
                if (!is_integer_btype(vtop->type.t & VT_BTYPE))
                    tcc_error(-1, "size of variable length array should be an integer");
                t1 = VT_VLA;
            }
        }
        skip(']');
        /* parse next post type */
        post_type(type, ad, storage, 0);
        if (type->t == VT_FUNC)
            tcc_error(-1, "declaration of an array of functions");
        t1 |= type->t & VT_VLA;
        
        if (t1 & VT_VLA) {
            loc -= type_size(&int_type, &align);
            loc &= -align;
            n = loc;

            vla_runtime_type_size(type, &align);
            gen_op('*');
            vset(&int_type, VT_LOCAL|VT_LVAL, n);
            vswap();
            vstore();
        }
        if (n != -1)
            vpop();
	nocode_wanted = saved_nocode_wanted;
                
        /* we push an anonymous symbol which will contain the array
           element type */
        s = sym_push(SYM_FIELD, type, 0, n);
        type->t = (t1 ? VT_VLA : VT_ARRAY) | VT_PTR;
        type->ref = s;
    }
    return 1;
}

/* Parse a type declarator (except basic type), and return the type
   in 'type'. 'td' is a bitmask indicating which kind of type decl is
   expected. 'type' should contain the basic type. 'ad' is the
   attribute definition of the basic type. It can be modified by
   type_decl().  If this (possibly abstract) declarator is a pointer chain
   it returns the innermost pointed to type (equals *type, but is a different
   pointer), otherwise returns type itself, that's used for recursive calls.  */
static CType *type_decl(CType *type, AttributeDef *ad, int *v, int td)
{
    CType *post, *ret;
    int qualifiers, storage;

    /* recursive type, remove storage bits first, apply them later again */
    storage = type->t & VT_STORAGE;
    type->t &= ~VT_STORAGE;
    post = ret = type;

    while (tok == '*') {
        qualifiers = 0;
    redo:
        next();
        switch(tok) {
        case TOK_CONST1:
        case TOK_CONST2:
        case TOK_CONST3:
            qualifiers |= VT_CONSTANT;
            goto redo;
        case TOK_VOLATILE1:
        case TOK_VOLATILE2:
        case TOK_VOLATILE3:
            qualifiers |= VT_VOLATILE;
            goto redo;
        case TOK_RESTRICT1:
        case TOK_RESTRICT2:
        case TOK_RESTRICT3:
            goto redo;
	/* XXX: clarify attribute handling */
	case TOK_ATTRIBUTE1:
	case TOK_ATTRIBUTE2:
	    parse_attribute(ad);
	    break;
        }
        mk_pointer(type);
        type->t |= qualifiers;
	if (ret == type)
	    /* innermost pointed to type is the one for the first derivation */
	    ret = pointed_type(type);
    }

    if (tok == '(') {
	/* This is possibly a parameter type list for abstract declarators
	   ('int ()'), use post_type for testing this.  */
	if (!post_type(type, ad, 0, td)) {
	    /* It's not, so it's a nested declarator, and the post operations
	       apply to the innermost pointed to type (if any).  */
	    /* XXX: this is not correct to modify 'ad' at this point, but
	       the syntax is not clear */
	    parse_attribute(ad);
	    post = type_decl(type, ad, v, td);
	    skip(')');
	}
    } else if (tok >= TOK_IDENT && (td & TYPE_DIRECT)) {
	/* type identifier */
	*v = tok;
	next();
    } else {
	if( !(td & TYPE_ABSTRACT ))  tcc_error(-1, "identifier expected" );
	*v = 0;
    }
    post_type(post, ad, storage, 0);
    parse_attribute(ad);
    type->t |= storage;
    return ret;
}

/* compute the lvalue VT_LVAL_xxx needed to match type t. */
ST_FUNC int lvalue_type(int t)
{
    int bt, r;
    r = VT_LVAL;
    bt = t & VT_BTYPE;
    if (bt == VT_BYTE || bt == VT_BOOL)
        r |= VT_LVAL_BYTE;
    else if (bt == VT_SHORT)
        r |= VT_LVAL_SHORT;
    else
        return r;
    if (t & VT_UNSIGNED)
        r |= VT_LVAL_UNSIGNED;
    return r;
}

/* indirection with full error checking and bound check */
ST_FUNC void indir(void)
{
    if ((vtop->type.t & VT_BTYPE) != VT_PTR) {
        if(( vtop->type.t & VT_BTYPE ) == VT_FUNC )  return;
        tcc_error(-1, "pointer expected" );
    }
    if (vtop->r & VT_LVAL)
        gv(RC_INT);
    vtop->type = *pointed_type(&vtop->type);
    /* Arrays and functions are never lvalues */
    if (!(vtop->type.t & VT_ARRAY) && !(vtop->type.t & VT_VLA)
        && (vtop->type.t & VT_BTYPE) != VT_FUNC) {
        vtop->r |= lvalue_type(vtop->type.t);
        /* if bound checking, the referenced pointer must be checked */
#ifdef CONFIG_TCC_BCHECK
        if( tcc_state->do_bounds_check )  vtop->r |= VT_MUSTBOUND;
#endif
    }
}

/* pass a parameter to a function and do type checking and casting */
static void gfunc_param_typed(Sym *func, Sym *arg)
{
    int func_type;
    CType type;

    func_type = func->f.func_type;
    if (func_type == FUNC_OLD ||
        (func_type == FUNC_ELLIPSIS && arg == NULL)) {
        /* default casting : only need to convert float to double */
        if ((vtop->type.t & VT_BTYPE) == VT_FLOAT) {
            gen_cast_s(VT_DOUBLE);
        } else if (vtop->type.t & VT_BITFIELD) {
            type.t = vtop->type.t & (VT_BTYPE | VT_UNSIGNED);
	    type.ref = vtop->type.ref;
            gen_cast(&type);
        }
    } else if (arg == NULL) {
        tcc_error(-1, "too many arguments to function");
    } else {
        type = arg->type;
        type.t &= ~VT_CONSTANT; /* need to do that to avoid false warning */
        gen_assign_cast(&type);
    }
}

/* parse an expression and return its type without any side effect. */
static void expr_type(CType *type, void (*expr_fn)(void))
{
    nocode_wanted++;
    expr_fn();
    *type = vtop->type;
    vpop();
    nocode_wanted--;
}

/* parse an expression of the form '(type)' or '(expr)' and return its
   type */
static void parse_expr_type(CType *type)
{
    int n;
    AttributeDef ad;

    skip('(');
    if (parse_btype(type, &ad)) {
        type_decl(type, &ad, &n, TYPE_ABSTRACT);
    } else {
        expr_type(type, gexpr);
    }
    skip(')');
}

static void parse_type( CType * type ) {
    AttributeDef ad;
    int n;
    if( !parse_btype( type, &ad ))  tcc_error(-1, "type expected" );
    type_decl(type, &ad, &n, TYPE_ABSTRACT);
}

static void parse_builtin_params(int nc, const char *args)
{
    char c, sep = '(';
    CType t;
    if (nc)
        nocode_wanted++;
    next();
    while ((c = *args++)) {
	skip(sep);
	sep = ',';
	switch (c) {
	    case 'e': expr_eq(); continue;
	    case 't': parse_type(&t); vpush(&t); continue;
	    default: tcc_error(-1, "internal error"); break;
	}
    }
    skip(')');
    if (nc)
        nocode_wanted--;
}

ST_FUNC void unary(void)
{
    int n, t, align, size, r, sizeof_caller;
    CType type;
    Sym *s;
    AttributeDef ad;

    sizeof_caller = in_sizeof;
    in_sizeof = 0;
    type.ref = NULL;
    /* XXX: GCC 2.95.3 does not generate a table although it should be
       better here */
 tok_next:
    switch(tok) {
    case TOK_EXTENSION:
        next();
        goto tok_next;
    case TOK_LCHAR:
#ifdef TCC_TARGET_PE
        t = VT_SHORT|VT_UNSIGNED;
        goto push_tokc;
#endif
    case TOK_CINT:
    case TOK_CCHAR: 
	t = VT_INT;
 push_tokc:
	type.t = t;
	vsetc(&type, VT_CONST, &tokc);
        next();
        break;
    case TOK_CUINT:
        t = VT_INT | VT_UNSIGNED;
        goto push_tokc;
    case TOK_CLLONG:
        t = VT_LLONG;
	goto push_tokc;
    case TOK_CULLONG:
        t = VT_LLONG | VT_UNSIGNED;
	goto push_tokc;
    case TOK_CFLOAT:
        t = VT_FLOAT;
	goto push_tokc;
    case TOK_CDOUBLE:
        t = VT_DOUBLE;
	goto push_tokc;
    case TOK_CLDOUBLE:
        t = VT_LDOUBLE;
	goto push_tokc;
    case TOK_CLONG:
        t = (LONG_SIZE == 8 ? VT_LLONG : VT_INT) | VT_LONG;
	goto push_tokc;
    case TOK_CULONG:
        t = (LONG_SIZE == 8 ? VT_LLONG : VT_INT) | VT_LONG | VT_UNSIGNED;
	goto push_tokc;
    case TOK___FUNCTION__:
        if (!gnu_ext)
            goto tok_identifier;
        /* fall thru */
    case TOK___FUNC__:
        {
            void *ptr;
            int len;
            /* special function name identifier */
            len = strlen(funcname) + 1;
            /* generate char[len] type */
            type.t = VT_BYTE;
            mk_pointer(&type);
            type.t |= VT_ARRAY;
            type.ref->c = len;
            vpush_ref(&type, data_section, data_section->data_offset, len);
            if (!NODATA_WANTED) {
                ptr = section_ptr_add(data_section, len);
                memcpy(ptr, funcname, len);
            }
            next();
        }
        break;
    case TOK_LSTR:
#ifdef TCC_TARGET_PE
        t = VT_SHORT | VT_UNSIGNED;
#else
        t = VT_INT;
#endif
        goto str_init;
    case TOK_STR:
        /* string parsing */
        t = VT_BYTE;
        if (tcc_state->char_is_unsigned)
            t = VT_BYTE | VT_UNSIGNED;
    str_init:
        if (tcc_state->warn_write_strings)
            t |= VT_CONSTANT;
        type.t = t;
        mk_pointer(&type);
        type.t |= VT_ARRAY;
        memset(&ad, 0, sizeof(AttributeDef));
        decl_initializer_alloc(&type, &ad, VT_CONST, 2, 0, 0);
        break;
    case '(':
        next();
        /* cast ? */
        if (parse_btype(&type, &ad)) {
            type_decl(&type, &ad, &n, TYPE_ABSTRACT);
            skip(')');
            /* check ISOC99 compound literal */
            if (tok == '{') {
                    /* data is allocated locally by default */
                if (global_expr)
                    r = VT_CONST;
                else
                    r = VT_LOCAL;
                /* all except arrays are lvalues */
                if (!(type.t & VT_ARRAY))
                    r |= lvalue_type(type.t);
                memset(&ad, 0, sizeof(AttributeDef));
                decl_initializer_alloc(&type, &ad, r, 1, 0, 0);
            } else {
                if (sizeof_caller) {
                    vpush(&type);
                    return;
                }
                unary();
                gen_cast(&type);
            }
        } else if (tok == '{') {
	    int saved_nocode_wanted = nocode_wanted;
            if( const_wanted )  tcc_error(-1, "expected constant");
            /* save all registers */
            save_regs(0);
            /* statement expression : we do not accept break/continue
               inside as GCC does.  We do retain the nocode_wanted state,
	       as statement expressions can't ever be entered from the
	       outside, so any reactivation of code emission (from labels
	       or loop heads) can be disabled again after the end of it. */
            block(NULL, NULL, 1);
	    nocode_wanted = saved_nocode_wanted;
            skip(')');
        } else {
            gexpr();
            skip(')');
        }
        break;
    case '*':
        next();
        unary();
        indir();
        break;
    case '&':
        next();
        unary();
        /* functions names must be treated as function pointers,
           except for unary '&' and sizeof. Since we consider that
           functions are not lvalues, we only have to handle it
           there and in function calls. */
        /* arrays can also be used although they are not lvalues */
        if ((vtop->type.t & VT_BTYPE) != VT_FUNC &&
            !(vtop->type.t & VT_ARRAY))
            test_lvalue();
        mk_pointer(&vtop->type);
        gaddrof();
        break;
    case '!':
        next();
        unary();
        if ((vtop->r & (VT_VALMASK | VT_LVAL | VT_SYM)) == VT_CONST) {
            gen_cast_s(VT_BOOL);
            vtop->c.i = !vtop->c.i;
        } else if ((vtop->r & VT_VALMASK) == VT_CMP)
            vtop->c.i ^= 1;
        else {
            save_regs(1);
            vseti(VT_JMP, gvtst(1, 0));
        }
        break;
    case '~':
        next();
        unary();
        vpushi(-1);
        gen_op('^');
        break;
    case '+':
        next();
        unary();
        if ((vtop->type.t & VT_BTYPE) == VT_PTR)
            tcc_error(-1, "pointer not accepted for unary plus");
        /* In order to force cast, we add zero, except for floating point
	   where we really need an noop (otherwise -0.0 will be transformed
	   into +0.0).  */
	if (!is_float(vtop->type.t)) {
	    vpushi(0);
	    gen_op('+');
	}
        break;
    case TOK_SIZEOF:
    case TOK_ALIGNOF1:
    case TOK_ALIGNOF2:
        t = tok;
        next();
        in_sizeof++;
        expr_type(&type, unary); /* Perform a in_sizeof = 0; */
        s = vtop[1].sym; /* hack: accessing previous vtop */
        size = type_size(&type, &align);
        if (s && s->a.aligned)
            align = 1 << (s->a.aligned - 1);
        if (t == TOK_SIZEOF) {
            if (!(type.t & VT_VLA)) {
                if (size < 0)
                    tcc_error(-1, "sizeof applied to an incomplete type");
                vpushs(size);
            } else {
                vla_runtime_type_size(&type, &align);
            }
        } else {
            vpushs(align);
        }
        vtop->type.t |= VT_UNSIGNED;
        break;

    case TOK_builtin_expect:
	/* __builtin_expect is a no-op for now */
	parse_builtin_params(0, "ee");
	vpop();
        break;
    case TOK_builtin_types_compatible_p:
	parse_builtin_params(0, "tt");
	vtop[-1].type.t &= ~(VT_CONSTANT | VT_VOLATILE);
	vtop[0].type.t &= ~(VT_CONSTANT | VT_VOLATILE);
	n = is_compatible_types(&vtop[-1].type, &vtop[0].type);
	vtop -= 2;
	vpushi(n);
        break;
    case TOK_builtin_choose_expr:
	{
	    int64_t c;
	    next();
	    skip('(');
	    c = expr_const64();
	    skip(',');
	    if (!c) {
		nocode_wanted++;
	    }
	    expr_eq();
	    if (!c) {
		vpop();
		nocode_wanted--;
	    }
	    skip(',');
	    if (c) {
		nocode_wanted++;
	    }
	    expr_eq();
	    if (c) {
		vpop();
		nocode_wanted--;
	    }
	    skip(')');
	}
        break;
    case TOK_builtin_constant_p:
	parse_builtin_params(1, "e");
	n = (vtop->r & (VT_VALMASK | VT_LVAL | VT_SYM)) == VT_CONST;
	vtop--;
	vpushi(n);
        break;
    case TOK_builtin_frame_address:
    case TOK_builtin_return_address:
        {
            int tok1 = tok;
            int level;
            next();
            skip('(');
            if (tok != TOK_CINT) {
                tcc_error(-1, "%s only takes positive integers",
                          tok1 == TOK_builtin_return_address ?
                          "__builtin_return_address" :
                          "__builtin_frame_address");
            }
            level = (uint32_t)tokc.i;
            next();
            skip(')');
            type.t = VT_VOID;
            mk_pointer(&type);
            vset(&type, VT_LOCAL, 0);       /* local frame */
            while (level--) {
                mk_pointer(&vtop->type);
                indir();                    /* -> parent frame */
            }
            if (tok1 == TOK_builtin_return_address) {
                // assume return address is just above frame pointer on stack
                vpushi(PTR_SIZE);
                gen_op('+');
                mk_pointer(&vtop->type);
                indir();
            }
        }
        break;
#ifdef TCC_TARGET_X86_64
#ifdef TCC_TARGET_PE
    case TOK_builtin_va_start:
	parse_builtin_params(0, "ee");
        r = vtop->r & VT_VALMASK;
        if( r == VT_LLOCAL )  r = VT_LOCAL;
        if( r != VT_LOCAL )  tcc_error(-1, "__builtin_va_start expects a local variable" );
        vtop->r = r;
	vtop->type = char_pointer_type;
	vtop->c.i += 8;
	vstore();
        break;
#else
    case TOK_builtin_va_arg_types:
	parse_builtin_params(0, "t");
	vpushi(classify_x86_64_va_arg(&vtop->type));
	vswap();
	vpop();
        break;
#endif
#endif

#ifdef TCC_TARGET_ARM64
    case TOK___va_start: {
	parse_builtin_params(0, "ee");
        //xx check types
        gen_va_start();
        vpushi(0);
        vtop->type.t = VT_VOID;
        break;
    }
    case TOK___va_arg: {
	parse_builtin_params(0, "et");
	type = vtop->type;
	vpop();
        //xx check types
        gen_va_arg(&type);
        vtop->type = type;
        break;
    }
    case TOK___arm64_clear_cache: {
	parse_builtin_params(0, "ee");
        gen_clear_cache();
        vpushi(0);
        vtop->type.t = VT_VOID;
        break;
    }
#endif
    /* pre operations */
    case TOK_INC:
    case TOK_DEC:
        t = tok;
        next();
        unary();
        inc(0, t);
        break;
    case '-':
        next();
        unary();
        t = vtop->type.t & VT_BTYPE;
	if (is_float(t)) {
            /* In IEEE negate(x) isn't subtract(0,x), but rather
	       subtract(-0, x).  */
	    vpush(&vtop->type);
	    if (t == VT_FLOAT)
	        vtop->c.f = -1.0 * 0.0;
	    else if (t == VT_DOUBLE)
	        vtop->c.d = -1.0 * 0.0;
	    else
	        vtop->c.ld = -1.0 * 0.0;
	} else
	    vpushi(0);
	vswap();
	gen_op('-');
        break;
    case TOK_LAND:
        if (!gnu_ext)
            goto tok_identifier;
        next();
        /* allow to take the address of a label */
        if( tok < TOK_UIDENT )  tcc_error(-1, "label identifier" );
        s = label_find(tok);
        if( !s )  s = label_push( &global_label_stack, tok, LABEL_FORWARD );
        else {
            if (s->r == LABEL_DECLARED)
                s->r = LABEL_FORWARD;
        }
        if (!s->type.t) {
            s->type.t = VT_VOID;
            mk_pointer(&s->type);
            s->type.t |= VT_STATIC;
        }
        vpushsym(&s->type, s);
        next();
        break;

    case TOK_GENERIC:
    {
	CType controlling_type;
	int has_default = 0;
	int has_match = 0;
	int learn = 0;
	TokenString *str = NULL;

	next();
	skip('(');
	expr_type(&controlling_type, expr_eq);
	controlling_type.t &= ~(VT_CONSTANT | VT_VOLATILE | VT_ARRAY);
	for (;;) {
	    learn = 0;
	    skip(',');
	    if (tok == TOK_DEFAULT) {
		if (has_default)
		    tcc_error(-1, "too many 'default'");
		has_default = 1;
		if (!has_match)
		    learn = 1;
		next();
	    } else {
	        AttributeDef ad_tmp;
		int itmp;
	        CType cur_type;
		parse_btype(&cur_type, &ad_tmp);
		type_decl(&cur_type, &ad_tmp, &itmp, TYPE_ABSTRACT);
		if (compare_types(&controlling_type, &cur_type, 0)) {
		    if (has_match) {
		      tcc_error(-1, "type match twice");
		    }
		    has_match = 1;
		    learn = 1;
		}
	    }
	    skip(':');
	    if (learn) {
		if (str)
		    tok_str_free(str);
		skip_or_save_block(&str);
	    } else {
		skip_or_save_block(NULL);
	    }
	    if (tok == ')')
		break;
	}
	if (!str) {
	    char buf[60];
	    type_to_str(buf, sizeof buf, &controlling_type, NULL);
	    tcc_error(-1, "type '%s' does not match any association", buf);
	}
	begin_macro(str, 1);
	next();
	expr_eq();
	if( tok != TOK_EOF )  tcc_error(-1, ", expected" );
	end_macro();
        next();
	break;
    }
    // special qnan , snan and infinity values
    case TOK___NAN__:
        vpush64(VT_DOUBLE, 0x7ff8000000000000ULL);
        next();
        break;
    case TOK___SNAN__:
        vpush64(VT_DOUBLE, 0x7ff0000000000001ULL);
        next();
        break;
    case TOK___INF__:
        vpush64(VT_DOUBLE, 0x7ff0000000000000ULL);
        next();
        break;

    default:
    tok_identifier:
        t = tok;
        next();
        if( t < TOK_UIDENT )  tcc_error(-1, "identifier expected" );
        s = sym_find(t);
        if (!s || IS_ASM_SYM(s)) {
            const char *name = get_tok_str(t, NULL);
            if (tok != '(')
                tcc_error(-1, "'%s' undeclared", name);
            /* for simple function calls, we tolerate undeclared
               external reference to int() function */
            if (tcc_state->warn_implicit_function_declaration
            )
                tcc_error(0, "implicit declaration of function '%s'", name);
            s = external_global_sym(t, &func_old_type, 0); 
        }

        r = s->r;
        /* A symbol that has a register is a local register variable,
           which starts out as VT_LOCAL value.  */
        if ((r & VT_VALMASK) < VT_CONST)
            r = (r & ~VT_VALMASK) | VT_LOCAL;

        vset(&s->type, r, s->c);
        /* Point to s as backpointer (even without r&VT_SYM).
	   Will be used by at least the x86 inline asm parser for
	   regvars.  */
	vtop->sym = s;

        if (r & VT_SYM) {
            vtop->c.i = 0;
        } else if (r == VT_CONST && IS_ENUM_VAL(s->type.t)) {
            vtop->c.i = s->enum_val;
        }
        break;
    }
    
    /* post operations */
    while (1) {
        if (tok == TOK_INC || tok == TOK_DEC) {
            inc(1, tok);
            next();
        } else if (tok == '.' || tok == TOK_ARROW || tok == TOK_CDOUBLE) {
            int qualifiers;
            /* field */ 
            if (tok == TOK_ARROW) 
                indir();
            qualifiers = vtop->type.t & (VT_CONSTANT | VT_VOLATILE);
            test_lvalue();
            gaddrof();
            /* expect pointer on structure */
            if(( vtop->type.t & VT_BTYPE ) != VT_STRUCT )  tcc_error(-1, "struct or union expected" );
            if( tok == TOK_CDOUBLE )  tcc_error(-1, "field name expected" );
            next();
            if( tok == TOK_CINT || tok == TOK_CUINT )  tcc_error(-1, "field name expected" );
	    s = find_field(&vtop->type, tok);
            if (!s)
                tcc_error(-1, "field not found: %s",  get_tok_str(tok & ~SYM_FIELD, &tokc));
            /* add field offset to pointer */
            vtop->type = char_pointer_type; /* change type to 'char *' */
            vpushi(s->c);
            gen_op('+');
            /* change type to field type, and set to lvalue */
            vtop->type = s->type;
            vtop->type.t |= qualifiers;
            /* an array is never an lvalue */
            if (!(vtop->type.t & VT_ARRAY)) {
                vtop->r |= lvalue_type(vtop->type.t);
#ifdef CONFIG_TCC_BCHECK
                /* if bound checking, the referenced pointer must be checked */
                if(tcc_state->do_bounds_check && (vtop->r & VT_VALMASK) != VT_LOCAL)  vtop->r |= VT_MUSTBOUND;
#endif
            }
            next();
        } else if (tok == '[') {
            next();
            gexpr();
            gen_op('+');
            indir();
            skip(']');
        } else if (tok == '(') {
            SValue ret;
            Sym *sa;
            int nb_args, ret_nregs, ret_align, regsize, variadic;

            /* function call  */
            if ((vtop->type.t & VT_BTYPE) != VT_FUNC) {
                /* pointer test (no array accepted) */
                if(( vtop->type.t & (VT_BTYPE | VT_ARRAY)) == VT_PTR ) {
                    vtop->type = *pointed_type(&vtop->type);
                    if(( vtop->type.t & VT_BTYPE ) != VT_FUNC )  goto error__func;
                }
                else {
                error__func:  tcc_error(-1, "function pointer expected" );
                }
            } else {
                vtop->r &= ~VT_LVAL; /* no lvalue */
            }
            /* get return type */
            s = vtop->type.ref;
            next();
            sa = s->next; /* first parameter */
            nb_args = regsize = 0;
            ret.r2 = VT_CONST;
            /* compute first implicit argument if a structure is returned */
            if ((s->type.t & VT_BTYPE) == VT_STRUCT) {
                variadic = (s->f.func_type == FUNC_ELLIPSIS);
                ret_nregs = gfunc_sret(&s->type, variadic, &ret.type,
                                       &ret_align, &regsize);
                if (!ret_nregs) {
                    /* get some space for the returned structure */
                    size = type_size(&s->type, &align);
#ifdef TCC_TARGET_ARM64
                /* On arm64, a small struct is return in registers.
                   It is much easier to write it to memory if we know
                   that we are allowed to write some extra bytes, so
                   round the allocated space up to a power of 2: */
                if (size < 16)
                    while (size & (size - 1))
                        size = (size | (size - 1)) + 1;
#endif
                    loc = (loc - size) & -align;
                    ret.type = s->type;
                    ret.r = VT_LOCAL | VT_LVAL;
                    /* pass it as 'int' to avoid structure arg passing
                       problems */
                    vseti(VT_LOCAL, loc);
                    ret.c = vtop->c;
                    nb_args++;
                }
            } else {
                ret_nregs = 1;
                ret.type = s->type;
            }

            if (ret_nregs) {
                /* return in register */
                if (is_float(ret.type.t)) {
                    ret.r = reg_fret(ret.type.t);
#ifdef TCC_TARGET_X86_64
                    if ((ret.type.t & VT_BTYPE) == VT_QFLOAT)
                      ret.r2 = REG_QRET;
#endif
                } else {
#ifndef TCC_TARGET_ARM64
#ifdef TCC_TARGET_X86_64
                    if ((ret.type.t & VT_BTYPE) == VT_QLONG)
#else
                    if ((ret.type.t & VT_BTYPE) == VT_LLONG)
#endif
                        ret.r2 = REG_LRET;
#endif
                    ret.r = REG_IRET;
                }
                ret.c.i = 0;
            }
            if (tok != ')') {
                for(;;) {
                    expr_eq();
                    gfunc_param_typed(s, sa);
                    nb_args++;
                    if (sa)
                        sa = sa->next;
                    if (tok == ')')
                        break;
                    skip(',');
                }
            }
            if (sa)
                tcc_error(-1, "too few arguments to function");
            skip(')');
            gfunc_call(nb_args);

            /* return value */
            for (r = ret.r + ret_nregs + !ret_nregs; r-- > ret.r;) {
                vsetc(&ret.type, r, &ret.c);
                vtop->r2 = ret.r2; /* Loop only happens when r2 is VT_CONST */
            }

            /* handle packed struct return */
            if (((s->type.t & VT_BTYPE) == VT_STRUCT) && ret_nregs) {
                int addr, offset;

                size = type_size(&s->type, &align);
		/* We're writing whole regs often, make sure there's enough
		   space.  Assume register size is power of 2.  */
		if (regsize > align)
		  align = regsize;
                loc = (loc - size) & -align;
                addr = loc;
                offset = 0;
                for (;;) {
                    vset(&ret.type, VT_LOCAL | VT_LVAL, addr + offset);
                    vswap();
                    vstore();
                    vtop--;
                    if (--ret_nregs == 0)
                        break;
                    offset += regsize;
                }
                vset(&s->type, VT_LOCAL | VT_LVAL, addr);
            }
        } else {
            break;
        }
    }
}

ST_FUNC void expr_prod(void)
{
    int t;

    unary();
    while (tok == '*' || tok == '/' || tok == '%') {
        t = tok;
        next();
        unary();
        gen_op(t);
    }
}

ST_FUNC void expr_sum(void)
{
    int t;

    expr_prod();
    while (tok == '+' || tok == '-') {
        t = tok;
        next();
        expr_prod();
        gen_op(t);
    }
}

static void expr_shift(void)
{
    int t;

    expr_sum();
    while (tok == TOK_SHL || tok == TOK_SAR) {
        t = tok;
        next();
        expr_sum();
        gen_op(t);
    }
}

static void expr_cmp(void)
{
    int t;

    expr_shift();
    while ((tok >= TOK_ULE && tok <= TOK_GT) ||
           tok == TOK_ULT || tok == TOK_UGE) {
        t = tok;
        next();
        expr_shift();
        gen_op(t);
    }
}

static void expr_cmpeq(void)
{
    int t;

    expr_cmp();
    while (tok == TOK_EQ || tok == TOK_NE) {
        t = tok;
        next();
        expr_cmp();
        gen_op(t);
    }
}

static void expr_and(void)
{
    expr_cmpeq();
    while (tok == '&') {
        next();
        expr_cmpeq();
        gen_op('&');
    }
}

static void expr_xor(void)
{
    expr_and();
    while (tok == '^') {
        next();
        expr_and();
        gen_op('^');
    }
}

static void expr_or(void)
{
    expr_xor();
    while (tok == '|') {
        next();
        expr_xor();
        gen_op('|');
    }
}

static void expr_land(void)
{
    expr_or();
    if (tok == TOK_LAND) {
	int t = 0;
	for(;;) {
	    if ((vtop->r & (VT_VALMASK | VT_LVAL | VT_SYM)) == VT_CONST) {
                gen_cast_s(VT_BOOL);
		if (vtop->c.i) {
		    vpop();
		} else {
		    nocode_wanted++;
		    while (tok == TOK_LAND) {
			next();
			expr_or();
			vpop();
		    }
		    nocode_wanted--;
		    if (t)
		      gsym(t);
		    gen_cast_s(VT_INT);
		    break;
		}
	    } else {
		if (!t)
		  save_regs(1);
		t = gvtst(1, t);
	    }
	    if (tok != TOK_LAND) {
		if (t)
		  vseti(VT_JMPI, t);
		else
		  vpushi(1);
		break;
	    }
	    next();
	    expr_or();
	}
    }
}

static void expr_lor(void)
{
    expr_land();
    if (tok == TOK_LOR) {
	int t = 0;
	for(;;) {
	    if ((vtop->r & (VT_VALMASK | VT_LVAL | VT_SYM)) == VT_CONST) {
                gen_cast_s(VT_BOOL);
		if (!vtop->c.i) {
		    vpop();
		} else {
		    nocode_wanted++;
		    while (tok == TOK_LOR) {
			next();
			expr_land();
			vpop();
		    }
		    nocode_wanted--;
		    if (t)
		      gsym(t);
		    gen_cast_s(VT_INT);
		    break;
		}
	    } else {
		if (!t)
		  save_regs(1);
		t = gvtst(0, t);
	    }
	    if (tok != TOK_LOR) {
		if (t)
		  vseti(VT_JMP, t);
		else
		  vpushi(0);
		break;
	    }
	    next();
	    expr_land();
	}
    }
}

/* Assuming vtop is a value used in a conditional context
   (i.e. compared with zero) return 0 if it's false, 1 if
   true and -1 if it can't be statically determined.  */
static int condition_3way(void)
{
    int c = -1;
    if ((vtop->r & (VT_VALMASK | VT_LVAL)) == VT_CONST &&
	(!(vtop->r & VT_SYM) || !vtop->sym->a.weak)) {
	vdup();
        gen_cast_s(VT_BOOL);
	c = vtop->c.i;
	vpop();
    }
    return c;
}

static void expr_cond(void)
{
    int tt, u, r1, r2, rc, t1, t2, bt1, bt2, islv, c, g;
    SValue sv;
    CType type, type1, type2;

    expr_lor();
    if (tok == '?') {
        next();
	c = condition_3way();
        g = (tok == ':' && gnu_ext);
        if (c < 0) {
            /* needed to avoid having different registers saved in
               each branch */
            if (is_float(vtop->type.t)) {
                rc = RC_FLOAT;
#ifdef TCC_TARGET_X86_64
                if ((vtop->type.t & VT_BTYPE) == VT_LDOUBLE) {
                    rc = RC_ST0;
                }
#endif
            } else
                rc = RC_INT;
            gv(rc);
            save_regs(1);
            if (g)
                gv_dup();
            tt = gvtst(1, 0);

        } else {
            if (!g)
                vpop();
            tt = 0;
        }

        if (1) {
            if (c == 0)
                nocode_wanted++;
            if (!g)
                gexpr();

            type1 = vtop->type;
            sv = *vtop; /* save value to handle it later */
            vtop--; /* no vpop so that FP stack is not flushed */
            skip(':');

            u = 0;
            if (c < 0)
                u = gjmp(0);
            gsym(tt);

            if (c == 0)
                nocode_wanted--;
            if (c == 1)
                nocode_wanted++;
            expr_cond();
            if (c == 1)
                nocode_wanted--;

            type2 = vtop->type;
            t1 = type1.t;
            bt1 = t1 & VT_BTYPE;
            t2 = type2.t;
            bt2 = t2 & VT_BTYPE;
            type.ref = NULL;

            /* cast operands to correct type according to ISOC rules */
            if (is_float(bt1) || is_float(bt2)) {
                if (bt1 == VT_LDOUBLE || bt2 == VT_LDOUBLE) {
                    type.t = VT_LDOUBLE;

                } else if (bt1 == VT_DOUBLE || bt2 == VT_DOUBLE) {
                    type.t = VT_DOUBLE;
                } else {
                    type.t = VT_FLOAT;
                }
            } else if (bt1 == VT_LLONG || bt2 == VT_LLONG) {
                /* cast to biggest op */
                type.t = VT_LLONG | VT_LONG;
                if (bt1 == VT_LLONG)
                    type.t &= t1;
                if (bt2 == VT_LLONG)
                    type.t &= t2;
                /* convert to unsigned if it does not fit in a long long */
                if ((t1 & (VT_BTYPE | VT_UNSIGNED | VT_BITFIELD)) == (VT_LLONG | VT_UNSIGNED) ||
                    (t2 & (VT_BTYPE | VT_UNSIGNED | VT_BITFIELD)) == (VT_LLONG | VT_UNSIGNED))
                    type.t |= VT_UNSIGNED;
            } else if (bt1 == VT_PTR || bt2 == VT_PTR) {
		/* If one is a null ptr constant the result type
		   is the other.  */
		if (is_null_pointer (vtop))
		  type = type1;
		else if (is_null_pointer (&sv))
		  type = type2;
                /* XXX: test pointer compatibility, C99 has more elaborate
		   rules here.  */
		else
		  type = type1;
            } else if (bt1 == VT_FUNC || bt2 == VT_FUNC) {
                /* XXX: test function pointer compatibility */
                type = bt1 == VT_FUNC ? type1 : type2;
            } else if (bt1 == VT_STRUCT || bt2 == VT_STRUCT) {
                /* XXX: test structure compatibility */
                type = bt1 == VT_STRUCT ? type1 : type2;
            } else if (bt1 == VT_VOID || bt2 == VT_VOID) {
                /* NOTE: as an extension, we accept void on only one side */
                type.t = VT_VOID;
            } else {
                /* integer operations */
                type.t = VT_INT | (VT_LONG & (t1 | t2));
                /* convert to unsigned if it does not fit in an integer */
                if ((t1 & (VT_BTYPE | VT_UNSIGNED | VT_BITFIELD)) == (VT_INT | VT_UNSIGNED) ||
                    (t2 & (VT_BTYPE | VT_UNSIGNED | VT_BITFIELD)) == (VT_INT | VT_UNSIGNED))
                    type.t |= VT_UNSIGNED;
            }
            /* keep structs lvalue by transforming `(expr ? a : b)` to `*(expr ? &a : &b)` so
               that `(expr ? a : b).mem` does not error  with "lvalue expected" */
            islv = (vtop->r & VT_LVAL) && (sv.r & VT_LVAL) && VT_STRUCT == (type.t & VT_BTYPE);
            islv &= c < 0;

            /* now we convert second operand */
            if (c != 1) {
                gen_cast(&type);
                if (islv) {
                    mk_pointer(&vtop->type);
                    gaddrof();
                } else if (VT_STRUCT == (vtop->type.t & VT_BTYPE))
                    gaddrof();
            }

            rc = RC_INT;
            if (is_float(type.t)) {
                rc = RC_FLOAT;
#ifdef TCC_TARGET_X86_64
                if ((type.t & VT_BTYPE) == VT_LDOUBLE) {
                    rc = RC_ST0;
                }
#endif
            } else if ((type.t & VT_BTYPE) == VT_LLONG) {
                /* for long longs, we use fixed registers to avoid having
                   to handle a complicated move */
                rc = RC_IRET;
            }

            tt = r2 = 0;
            if (c < 0) {
                r2 = gv(rc);
                tt = gjmp(0);
            }
            gsym(u);

            /* this is horrible, but we must also convert first
               operand */
            if (c != 0) {
                *vtop = sv;
                gen_cast(&type);
                if (islv) {
                    mk_pointer(&vtop->type);
                    gaddrof();
                } else if (VT_STRUCT == (vtop->type.t & VT_BTYPE))
                    gaddrof();
            }

            if (c < 0) {
                r1 = gv(rc);
                move_reg(r2, r1, type.t);
                vtop->r = r2;
                gsym(tt);
                if (islv)
                    indir();
            }
        }
    }
}

static void expr_eq(void)
{
    int t;
    
    expr_cond();
    if (tok == '=' ||
        (tok >= TOK_A_MOD && tok <= TOK_A_DIV) ||
        tok == TOK_A_XOR || tok == TOK_A_OR ||
        tok == TOK_A_SHL || tok == TOK_A_SAR) {
        test_lvalue();
        t = tok;
        next();
        if (t == '=') {
            expr_eq();
        } else {
            vdup();
            expr_eq();
            gen_op(t & 0x7f);
        }
        vstore();
    }
}

ST_FUNC void gexpr(void)
{
    while (1) {
        expr_eq();
        if (tok != ',')
            break;
        vpop();
        next();
    }
}

/* parse a constant expression and return value in vtop.  */
static void expr_const1(void)
{
    const_wanted++;
    nocode_wanted++;
    expr_cond();
    nocode_wanted--;
    const_wanted--;
}

/* parse an integer constant and return its value. */
static inline int64_t expr_const64(void)
{
    int64_t c;
    expr_const1();
    if(( vtop->r & ( VT_VALMASK | VT_LVAL | VT_SYM )) != VT_CONST ) tcc_error(-1, "constant expression expected");
    c = vtop->c.i;
    vpop();
    return c;
}

/* parse an integer constant and return its value.
   Complain if it doesn't fit 32bit (signed or unsigned).  */
ST_FUNC int expr_const(void)
{
    int c;
    int64_t wc = expr_const64();
    c = wc;
    if (c != wc && (unsigned)c != wc)
        tcc_error(-1, "constant exceeds 32 bit");
    return c;
}

/* return the label token if current token is a label, otherwise
   return zero */
static int is_label(void)
{
    int last_tok;

    /* fast test first */
    if (tok < TOK_UIDENT)
        return 0;
    /* no need to save tokc because tok is an identifier */
    last_tok = tok;
    next();
    if (tok == ':') {
        return last_tok;
    } else {
        unget_tok(last_tok);
        return 0;
    }
}

#ifndef TCC_TARGET_ARM64
static void gfunc_return(CType *func_type)
{
    if ((func_type->t & VT_BTYPE) == VT_STRUCT) {
        CType type, ret_type;
        int ret_align, ret_nregs, regsize;
        ret_nregs = gfunc_sret(func_type, func_var, &ret_type,
                               &ret_align, &regsize);
        if (0 == ret_nregs) {
            /* if returning structure, must copy it to implicit
               first pointer arg location */
            type = *func_type;
            mk_pointer(&type);
            vset(&type, VT_LOCAL | VT_LVAL, func_vc);
            indir();
            vswap();
            /* copy structure value to pointer */
            vstore();
        } else {
            /* returning structure packed into registers */
            int r, size, addr, align;
            size = type_size(func_type,&align);
            if ((vtop->r != (VT_LOCAL | VT_LVAL) ||
                 (vtop->c.i & (ret_align-1)))
                && (align & (ret_align-1))) {
                loc = (loc - size) & -ret_align;
                addr = loc;
                type = *func_type;
                vset(&type, VT_LOCAL | VT_LVAL, addr);
                vswap();
                vstore();
                vpop();
                vset(&ret_type, VT_LOCAL | VT_LVAL, addr);
            }
            vtop->type = ret_type;
            if (is_float(ret_type.t))
                r = rc_fret(ret_type.t);
            else
                r = RC_IRET;

            if (ret_nregs == 1)
                gv(r);
            else {
                for (;;) {
                    vdup();
                    gv(r);
                    vpop();
                    if (--ret_nregs == 0)
                      break;
                    /* We assume that when a structure is returned in multiple
                       registers, their classes are consecutive values of the
                       suite s(n) = 2^n */
                    r <<= 1;
                    vtop->c.i += regsize;
                }
            }
        }
    } else if (is_float(func_type->t)) {
        gv(rc_fret(func_type->t));
    } else {
        gv(RC_IRET);
    }
    vtop--; /* NOT vpop() because on x86 it would flush the fp stack */
}
#endif

static int case_cmp(const void *pa, const void *pb)
{
    int64_t a = (*(struct case_t**) pa)->v1;
    int64_t b = (*(struct case_t**) pb)->v1;
    return a < b ? -1 : a > b;
}

static void gcase(struct case_t **base, int len, int *bsym)
{
    struct case_t *p;
    int e;
    int ll = (vtop->type.t & VT_BTYPE) == VT_LLONG;
    gv(RC_INT);
    while (len > 4) {
        /* binary search */
        p = base[len/2];
        vdup();
	if (ll)
	    vpushll(p->v2);
	else
	    vpushi(p->v2);
        gen_op(TOK_LE);
        e = gtst(1, 0);
        vdup();
	if (ll)
	    vpushll(p->v1);
	else
	    vpushi(p->v1);
        gen_op(TOK_GE);
        gtst_addr(0, p->sym); /* v1 <= x <= v2 */
        /* x < v1 */
        gcase(base, len/2, bsym);
        if (cur_switch->def_sym)
            gjmp_addr(cur_switch->def_sym);
        else
            *bsym = gjmp(*bsym);
        /* x > v2 */
        gsym(e);
        e = len/2 + 1;
        base += e; len -= e;
    }
    /* linear scan */
    while (len--) {
        p = *base++;
        vdup();
	if (ll)
	    vpushll(p->v2);
	else
	    vpushi(p->v2);
        if (p->v1 == p->v2) {
            gen_op(TOK_EQ);
            gtst_addr(0, p->sym);
        } else {
            gen_op(TOK_LE);
            e = gtst(1, 0);
            vdup();
	    if (ll)
	        vpushll(p->v1);
	    else
	        vpushi(p->v1);
            gen_op(TOK_GE);
            gtst_addr(0, p->sym);
            gsym(e);
        }
    }
}

static void block(int *bsym, int *csym, int is_expr)
{
    int a, b, c, d, cond;
    Sym *s;

#if defined CONFIG_TCC_GDEBUG
    /* generate line number info */
    if( tcc_state->do_debug )  tcc_debug_line(tcc_state);
#endif

    if (is_expr) {
        /* default return value is (void) */
        vpushi(0);
        vtop->type.t = VT_VOID;
    }

    if (tok == TOK_IF) {
        /* if test */
	int saved_nocode_wanted = nocode_wanted;
        next();
        skip('(');
        gexpr();
        skip(')');
	cond = condition_3way();
        if (cond == 1)
            a = 0, vpop();
        else
            a = gvtst(1, 0);
        if (cond == 0)
	    nocode_wanted |= 0x20000000;
        block(bsym, csym, 0);
	if (cond != 1)
	    nocode_wanted = saved_nocode_wanted;
        c = tok;
        if (c == TOK_ELSE) {
            next();
            d = gjmp(0);
            gsym(a);
	    if (cond == 1)
	        nocode_wanted |= 0x20000000;
            block(bsym, csym, 0);
            gsym(d); /* patch else jmp */
	    if (cond != 0)
		nocode_wanted = saved_nocode_wanted;
        } else
            gsym(a);
    } else if (tok == TOK_WHILE) {
	int saved_nocode_wanted;
	nocode_wanted &= ~0x20000000;
        next();
        d = ind;
        vla_sp_restore();
        skip('(');
        gexpr();
        skip(')');
        a = gvtst(1, 0);
        b = 0;
        ++local_scope;
	saved_nocode_wanted = nocode_wanted;
        block(&a, &b, 0);
	nocode_wanted = saved_nocode_wanted;
        --local_scope;
        gjmp_addr(d);
        gsym(a);
        gsym_addr(b, d);
    } else if (tok == '{') {
        Sym *llabel;
        int block_vla_sp_loc = vla_sp_loc, saved_vlas_in_scope = vlas_in_scope;

        next();
        /* record local declaration stack position */
        s = local_stack;
        llabel = local_label_stack;
        ++local_scope;
        
        /* handle local labels declarations */
        if (tok == TOK_LABEL) {
            next();
            for(;;) {
                if( tok < TOK_UIDENT )  tcc_error(-1, "label identifier expected" );
                label_push(&local_label_stack, tok, LABEL_DECLARED);
                next();
                if (tok == ',') {
                    next();
                } else {
                    skip(';');
                    break;
                }
            }
        }
        while (tok != '}') {
	    if ((a = is_label()))
		unget_tok(a);
	    else
	        decl(VT_LOCAL);
            if (tok != '}') {
                if (is_expr)
                    vpop();
                block(bsym, csym, is_expr);
            }
        }
        /* pop locally defined labels */
        label_pop(&local_label_stack, llabel, is_expr);
        /* pop locally defined symbols */
        --local_scope;
	/* In the is_expr case (a statement expression is finished here),
	   vtop might refer to symbols on the local_stack.  Either via the
	   type or via vtop->sym.  We can't pop those nor any that in turn
	   might be referred to.  To make it easier we don't roll back
	   any symbols in that case; some upper level call to block() will
	   do that.  We do have to remove such symbols from the lookup
	   tables, though.  sym_pop will do that.  */
	sym_pop(&local_stack, s, is_expr);

        /* Pop VLA frames and restore stack pointer if required */
        if (vlas_in_scope > saved_vlas_in_scope) {
            vla_sp_loc = saved_vlas_in_scope ? block_vla_sp_loc : vla_sp_root_loc;
            vla_sp_restore();
        }
        vlas_in_scope = saved_vlas_in_scope;
        
        next();
    } else if (tok == TOK_RETURN) {
        next();
        if (tok != ';') {
            gexpr();
            gen_assign_cast(&func_vt);
            if ((func_vt.t & VT_BTYPE) == VT_VOID)
                vtop--;
            else
                gfunc_return(&func_vt);
        }
        skip(';');
        /* jump unless last stmt in top-level block */
        if (tok != '}' || local_scope != 1)
            rsym = gjmp(rsym);
	nocode_wanted |= 0x20000000;
    } else if (tok == TOK_BREAK) {
        /* compute jump */
        if (!bsym)  tcc_error(-1, "cannot break");
        *bsym = gjmp(*bsym);
        next();
        skip(';');
	nocode_wanted |= 0x20000000;
    } else if (tok == TOK_CONTINUE) {
        /* compute jump */
        if (!csym)  tcc_error(-1, "cannot continue");
        vla_sp_restore_root();
        *csym = gjmp(*csym);
        next();
        skip(';');
    } else if (tok == TOK_FOR) {
        int e;
	int saved_nocode_wanted;
	nocode_wanted &= ~0x20000000;
        next();
        skip('(');
        s = local_stack;
        ++local_scope;
        if (tok != ';') {
            /* c99 for-loop init decl? */
            if (!decl0(VT_LOCAL, 1, NULL)) {
                /* no, regular for-loop init expr */
                gexpr();
                vpop();
            }
        }
        skip(';');
        d = ind;
        c = ind;
        vla_sp_restore();
        a = 0;
        b = 0;
        if (tok != ';') {
            gexpr();
            a = gvtst(1, 0);
        }
        skip(';');
        if (tok != ')') {
            e = gjmp(0);
            c = ind;
            vla_sp_restore();
            gexpr();
            vpop();
            gjmp_addr(d);
            gsym(e);
        }
        skip(')');
	saved_nocode_wanted = nocode_wanted;
        block(&a, &b, 0);
	nocode_wanted = saved_nocode_wanted;
        gjmp_addr(c);
        gsym(a);
        gsym_addr(b, c);
        --local_scope;
        sym_pop(&local_stack, s, 0);

    } else 
    if (tok == TOK_DO) {
	int saved_nocode_wanted;
	nocode_wanted &= ~0x20000000;
        next();
        a = 0;
        b = 0;
        d = ind;
        vla_sp_restore();
	saved_nocode_wanted = nocode_wanted;
        block(&a, &b, 0);
        skip(TOK_WHILE);
        skip('(');
        gsym(b);
	gexpr();
	c = gvtst(0, 0);
	gsym_addr(c, d);
	nocode_wanted = saved_nocode_wanted;
        skip(')');
        gsym(a);
        skip(';');
    } else
    if (tok == TOK_SWITCH) {
        struct switch_t *saved, sw;
	int saved_nocode_wanted = nocode_wanted;
	SValue switchval;
        next();
        skip('(');
        gexpr();
        skip(')');
	switchval = *vtop--;
        a = 0;
        b = gjmp(0); /* jump to first case */
        sw.p = NULL; sw.n = 0; sw.def_sym = 0;
        saved = cur_switch;
        cur_switch = &sw;
        block(&a, csym, 0);
	nocode_wanted = saved_nocode_wanted;
        a = gjmp(a); /* add implicit break */
        /* case lookup */
        gsym(b);
        qsort(sw.p, sw.n, sizeof(void*), case_cmp);
        for (b = 1; b < sw.n; b++)
            if (sw.p[b - 1]->v2 >= sw.p[b]->v1)
                tcc_error(-1, "duplicate case value");
        /* Our switch table sorting is signed, so the compared
           value needs to be as well when it's 64bit.  */
        if ((switchval.type.t & VT_BTYPE) == VT_LLONG)
            switchval.type.t &= ~VT_UNSIGNED;
        vpushv(&switchval);
        gcase(sw.p, sw.n, &a);
        vpop();
        if (sw.def_sym)
          gjmp_addr(sw.def_sym);
        dynarray_reset(&sw.p, &sw.n);
        cur_switch = saved;
        /* break label */
        gsym(a);
    } else
    if (tok == TOK_CASE) {
        struct case_t *cr = tcc_malloc(sizeof(struct case_t));
        if( !cur_switch )  tcc_error(-1, "switch expected" );
	nocode_wanted &= ~0x20000000;
        next();
        cr->v1 = cr->v2 = expr_const64();
        if (gnu_ext && tok == TOK_DOTS) {
            next();
            cr->v2 = expr_const64();
            if( cr->v2 < cr->v1 )  tcc_error(0, "empty case range");
        }
        cr->sym = ind;
        dynarray_add(&cur_switch->p, &cur_switch->n, cr);
        skip(':');
        is_expr = 0;
        goto block_after_label;
    } else 
    if (tok == TOK_DEFAULT) {
        next();
        skip(':');
        if( !cur_switch )  tcc_error(-1, "switch expected" );
        if( cur_switch->def_sym )  tcc_error(-1, "too many 'default'");
        cur_switch->def_sym = ind;
        is_expr = 0;
        goto block_after_label;
    } else
    if (tok == TOK_GOTO) {
        next();
        if (tok == '*' && gnu_ext) {
            /* computed goto */
            next();
            gexpr();
            if(( vtop->type.t & VT_BTYPE ) != VT_PTR )  tcc_error(-1, "pointer expected" );
            ggoto();
        } else if (tok >= TOK_UIDENT) {
            s = label_find(tok);
            /* put forward definition if needed */
            if (!s) {
                s = label_push(&global_label_stack, tok, LABEL_FORWARD);
            } else {
                if (s->r == LABEL_DECLARED)
                    s->r = LABEL_FORWARD;
            }
            vla_sp_restore_root();
	    if( s->r & LABEL_FORWARD )  s->jnext = gjmp(s->jnext);
            else  gjmp_addr(s->jnext);
            next();
        }
        else  tcc_error(-1, "label identifier expected" );
        skip(';');
    } else if (tok == TOK_ASM1 || tok == TOK_ASM2 || tok == TOK_ASM3) {
        asm_instr();
    } else {
        b = is_label();
        if (b) {
            /* label case */
	    next();
            s = label_find(b);
            if (s) {
                if (s->r == LABEL_DEFINED)
                    tcc_error(-1, "duplicate label '%s'", get_tok_str(s->v, NULL));
                gsym(s->jnext);
                s->r = LABEL_DEFINED;
            } else {
                s = label_push(&global_label_stack, b, LABEL_DEFINED);
            }
            s->jnext = ind;
            vla_sp_restore();
            /* we accept this, but it is a mistake */
        block_after_label:
	    nocode_wanted &= ~0x20000000;
            if( tok == '}' )  tcc_error(0, "deprecated use of label at end of compound statement");
            else {
                if (is_expr)
                    vpop();
                block(bsym, csym, is_expr);
            }
        } else {
            /* expression case */
            if (tok != ';') {
                if (is_expr) {
                    vpop();
                    gexpr();
                } else {
                    gexpr();
                    vpop();
                }
            }
            skip(';');
        }
    }
}

/* This skips over a stream of tokens containing balanced {} and ()
   pairs, stopping at outer ',' ';' and '}' (or matching '}' if we started
   with a '{').  If STR then allocates and stores the skipped tokens
   in *STR.  This doesn't check if () and {} are nested correctly,
   i.e. "({)}" is accepted.  */
static void skip_or_save_block(TokenString **str)
{
    int braces = tok == '{';
    int level = 0;
    if (str)
      *str = tok_str_alloc();

    while ((level > 0 || (tok != '}' && tok != ',' && tok != ';' && tok != ')'))) {
	int t;
	if (tok == TOK_EOF) {
	     if( str || level > 0 )  tcc_error(-1, "unexpected end of file");
	     else break;
	}
	if (str)
	  tok_str_add_tok(*str);
	t = tok;
	next();
	if (t == '{' || t == '(') {
	    level++;
	} else if (t == '}' || t == ')') {
	    level--;
	    if (level == 0 && braces && t == '}')
	      break;
	}
    }
    if (str) {
	tok_str_add(*str, -1);
	tok_str_add(*str, 0);
    }
}

#define EXPR_CONST 1
#define EXPR_ANY   2

static void parse_init_elem(int expr_type)
{
    int saved_global_expr;
    switch(expr_type) {
    case EXPR_CONST:
        /* compound literals must be allocated globally in this case */
        saved_global_expr = global_expr;
        global_expr = 1;
        expr_const1();
        global_expr = saved_global_expr;
        /* NOTE: symbols are accepted, as well as lvalue for anon symbols
	   (compound literals).  */
        if (((vtop->r & (VT_VALMASK | VT_LVAL)) != VT_CONST
	     && ((vtop->r & (VT_SYM|VT_LVAL)) != (VT_SYM|VT_LVAL)
		 || vtop->sym->v < SYM_FIRST_ANOM))
            )
            tcc_error(-1, "initializer element is not constant");
        break;
    case EXPR_ANY:
        expr_eq();
        break;
    }
}

/* put zeros for variable based init */
static void init_putz(Section *sec, unsigned long c, int size)
{
    if (sec) {
        /* nothing to do because globals are already set to zero */
    } else {
        vpush_global_sym(&func_old_type, TOK_memset);
        vseti(VT_LOCAL, c);
#ifdef TCC_TARGET_ARM
        vpushs(size);
        vpushi(0);
#else
        vpushi(0);
        vpushs(size);
#endif
        gfunc_call(3);
    }
}

/* t is the array or struct type. c is the array or struct
   address. cur_field is the pointer to the current
   field, for arrays the 'c' member contains the current start
   index.  'size_only' is true if only size info is needed (only used
   in arrays).  al contains the already initialized length of the
   current container (starting at c).  This returns the new length of that.  */
static int decl_designator(CType *type, Section *sec, unsigned long c,
                           Sym **cur_field, int size_only, int al)
{
    Sym *s, *f;
    int index, index_last, align, l, nb_elems, elem_size;
    unsigned long corig = c;

    elem_size = 0;
    nb_elems = 1;
    if (gnu_ext && (l = is_label()) != 0)
        goto struct_field;
    /* NOTE: we only support ranges for last designator */
    while (nb_elems == 1 && (tok == '[' || tok == '.')) {
        if (tok == '[') {
            if( !( type->t & VT_ARRAY ))  tcc_error(-1, "array type expected" );
            next();
            index = index_last = expr_const();
            if (tok == TOK_DOTS && gnu_ext) {
                next();
                index_last = expr_const();
            }
            skip(']');
            s = type->ref;
	    if (index < 0 || (s->c >= 0 && index_last >= s->c) || index_last < index)
	        tcc_error(-1, "invalid index");
            if (cur_field)  (*cur_field)->c = index_last;
            type = pointed_type(type);
            elem_size = type_size(type, &align);
            c += index * elem_size;
            nb_elems = index_last - index + 1;
        } else {
            next();
            l = tok;
        struct_field:
            next();
            if(( type->t & VT_BTYPE ) != VT_STRUCT )  tcc_error(-1, "struct/union type expected" );
	    f = find_field(type, l);
            if( !f )  tcc_error(-1, "field expected" );
            if (cur_field)
                *cur_field = f;
	    type = &f->type;
            c += f->c;
        }
        cur_field = NULL;
    }
    if (!cur_field) {
        if( tok == '=' )  next();
        else if( !gnu_ext )  tcc_error(-1, "= expected" );
    } else {
        if (type->t & VT_ARRAY) {
	    index = (*cur_field)->c;
	    if( type->ref->c >= 0 && index >= type->ref->c )  tcc_error(-1, "index too large");
            type = pointed_type(type);
            c += index * type_size(type, &align);
        }
        else {
            f = *cur_field;
	    while (f && (f->v & SYM_FIRST_ANOM) && (f->type.t & VT_BITFIELD))
	        *cur_field = f = f->next;
            if( !f )  tcc_error(-1, "too many field init");
	    type = &f->type;
            c += f->c;
        }
    }
    /* must put zero in holes (note that doing it that way
       ensures that it even works with designators) */
    if (!size_only && c - corig > al)
	init_putz(sec, corig + al, c - corig - al);
    decl_initializer(type, sec, c, 0, size_only);

    /* XXX: make it more general */
    if (!size_only && nb_elems > 1) {
        unsigned long c_end;
        uint8_t *src, *dst;
        int i;

        if (!sec) {
	    vset(type, VT_LOCAL|VT_LVAL, c);
	    for (i = 1; i < nb_elems; i++) {
		vset(type, VT_LOCAL|VT_LVAL, c + elem_size * i);
		vswap();
		vstore();
	    }
	    vpop();
        } else if (!NODATA_WANTED) {
	    c_end = c + nb_elems * elem_size;
	    if (c_end > sec->data_allocated)
	        section_realloc(sec, c_end);
	    src = sec->data + c;
	    dst = src;
	    for(i = 1; i < nb_elems; i++) {
		dst += elem_size;
		memcpy(dst, src, elem_size);
	    }
	}
    }
    c += nb_elems * type_size(type, &align);
    if (c - corig > al)
      al = c - corig;
    return al;
}

/* store a value or an expression directly in global data or in local array */
static void init_putv(CType *type, Section *sec, unsigned long c)
{
    int bt;
    void *ptr;
    CType dtype;

    dtype = *type;
    dtype.t &= ~VT_CONSTANT; /* need to do that to avoid false warning */

    if (sec) {
	int size, align;
        /* XXX: not portable */
        /* XXX: generate error if incorrect relocation */
        gen_assign_cast(&dtype);
        bt = type->t & VT_BTYPE;

        if ((vtop->r & VT_SYM)
            && bt != VT_PTR
            && bt != VT_FUNC
            && (bt != (PTR_SIZE == 8 ? VT_LLONG : VT_INT)
                || (type->t & VT_BITFIELD))
            && !((vtop->r & VT_CONST) && vtop->sym->v >= SYM_FIRST_ANOM)
            )
            tcc_error(-1, "initializer element is not computable at load time");

        if (NODATA_WANTED) {
            vtop--;
            return;
        }

	size = type_size(type, &align);
	section_reserve(sec, c + size);
        ptr = sec->data + c;

        /* XXX: make code faster ? */
	if ((vtop->r & (VT_SYM|VT_CONST)) == (VT_SYM|VT_CONST) &&
	    vtop->sym->v >= SYM_FIRST_ANOM &&
	    /* XXX This rejects compound literals like
	       '(void *){ptr}'.  The problem is that '&sym' is
	       represented the same way, which would be ruled out
	       by the SYM_FIRST_ANOM check above, but also '"string"'
	       in 'char *p = "string"' is represented the same
	       with the type being VT_PTR and the symbol being an
	       anonymous one.  That is, there's no difference in vtop
	       between '(void *){x}' and '&(void *){x}'.  Ignore
	       pointer typed entities here.  Hopefully no real code
	       will every use compound literals with scalar type.  */
	    (vtop->type.t & VT_BTYPE) != VT_PTR) {
	    /* These come from compound literals, memcpy stuff over.  */
	    Section *ssec;
	    ElfSym *esym;
	    ElfW_Rel *rel;
	    esym = elfsym(vtop->sym);
	    ssec = tcc_state->sections[esym->st_shndx];
	    memmove (ptr, ssec->data + esym->st_value, size);
	    if (ssec->reloc) {
		/* We need to copy over all memory contents, and that
		   includes relocations.  Use the fact that relocs are
		   created it order, so look from the end of relocs
		   until we hit one before the copied region.  */
		int num_relocs = ssec->reloc->data_offset / sizeof(*rel);
		rel = (ElfW_Rel*)(ssec->reloc->data + ssec->reloc->data_offset);
		while (num_relocs--) {
		    rel--;
		    if (rel->r_offset >= esym->st_value + size)
		      continue;
		    if (rel->r_offset < esym->st_value)
		      break;
		    /* Note: if the same fields are initialized multiple
		       times (possible with designators) then we possibly
		       add multiple relocations for the same offset here.
		       That would lead to wrong code, the last reloc needs
		       to win.  We clean this up later after the whole
		       initializer is parsed.  */
		    put_elf_reloca(symtab_section, sec,
				   c + rel->r_offset - esym->st_value,
				   ELFW(R_TYPE)(rel->r_info),
				   ELFW(R_SYM)(rel->r_info),
#if PTR_SIZE == 8
				   rel->r_addend
#else
				   0
#endif
				  );
		}
	    }
	} else {
            if (type->t & VT_BITFIELD) {
                int bit_pos, bit_size, bits, n;
                unsigned char *p, v, m;
                bit_pos = BIT_POS(vtop->type.t);
                bit_size = BIT_SIZE(vtop->type.t);
                p = (unsigned char*)ptr + (bit_pos >> 3);
                bit_pos &= 7, bits = 0;
                while (bit_size) {
                    n = 8 - bit_pos;
                    if (n > bit_size)
                        n = bit_size;
                    v = vtop->c.i >> bits << bit_pos;
                    m = ((1 << n) - 1) << bit_pos;
                    *p = (*p & ~m) | (v & m);
                    bits += n, bit_size -= n, bit_pos = 0, ++p;
                }
            } else
            switch(bt) {
		/* XXX: when cross-compiling we assume that each type has the
		   same representation on host and target, which is likely to
		   be wrong in the case of long double */
	    case VT_BOOL:
		vtop->c.i = vtop->c.i != 0;
	    case VT_BYTE:
		*(char *)ptr |= vtop->c.i;
		break;
	    case VT_SHORT:
		*(short *)ptr |= vtop->c.i;
		break;
	    case VT_FLOAT:
		*(float*)ptr = vtop->c.f;
		break;
	    case VT_DOUBLE:
		*(double *)ptr = vtop->c.d;
		break;
	    case VT_LDOUBLE:
#if defined TCC_IS_NATIVE_387
                if (sizeof (long double) >= 10) /* zero pad ten-byte LD */
                    memcpy(ptr, &vtop->c.ld, 10);
#ifdef __TINYC__
                else if (sizeof (long double) == sizeof (double))
                    __asm__("fldl %1\nfstpt %0\n" : "=m" (*ptr) : "m" (vtop->c.ld));
#endif
                else if (vtop->c.ld == 0.0)
                    ;
                else
#endif
                if (sizeof(long double) == LDOUBLE_SIZE)
		    *(long double*)ptr = vtop->c.ld;
                else if (sizeof(double) == LDOUBLE_SIZE)
		    *(double *)ptr = (double)vtop->c.ld;
                else  tcc_error(-1, "can't cross compile long double constants");
		break;
#if PTR_SIZE != 8
	    case VT_LLONG:
		*(long long *)ptr |= vtop->c.i;
		break;
#else
	    case VT_LLONG:
#endif
	    case VT_PTR:
		{
		    addr_t val = vtop->c.i;
#if PTR_SIZE == 8
		    if (vtop->r & VT_SYM)
		      greloca(sec, vtop->sym, c, R_DATA_PTR, val);
		    else
		      *(addr_t *)ptr |= val;
#else
		    if (vtop->r & VT_SYM)
		      greloc(sec, vtop->sym, c, R_DATA_PTR);
		    *(addr_t *)ptr |= val;
#endif
		    break;
		}
	    default:
		{
		    int val = vtop->c.i;
#if PTR_SIZE == 8
		    if (vtop->r & VT_SYM)
		      greloca(sec, vtop->sym, c, R_DATA_PTR, val);
		    else
		      *(int *)ptr |= val;
#else
		    if (vtop->r & VT_SYM)
		      greloc(sec, vtop->sym, c, R_DATA_PTR);
		    *(int *)ptr |= val;
#endif
		    break;
		}
	    }
	}
        vtop--;
    } else {
        vset(&dtype, VT_LOCAL|VT_LVAL, c);
        vswap();
        vstore();
        vpop();
    }
}

/* 't' contains the type and storage info. 'c' is the offset of the
   object in section 'sec'. If 'sec' is NULL, it means stack based
   allocation. 'first' is true if array '{' must be read (multi
   dimension implicit array init handling). 'size_only' is true if
   size only evaluation is wanted (only for arrays). */
static void decl_initializer(CType *type, Section *sec, unsigned long c, 
                             int first, int size_only)
{
    int len, n, no_oblock, nb, i;
    int size1, align1;
    int have_elem;
    Sym *s, *f;
    Sym indexsym;
    CType *t1;

    /* If we currently are at an '}' or ',' we have read an initializer
       element in one of our callers, and not yet consumed it.  */
    have_elem = tok == '}' || tok == ',';
    if (!have_elem && tok != '{' &&
	/* In case of strings we have special handling for arrays, so
	   don't consume them as initializer value (which would commit them
	   to some anonymous symbol).  */
	tok != TOK_LSTR && tok != TOK_STR &&
	!size_only) {
	parse_init_elem(!sec ? EXPR_ANY : EXPR_CONST);
	have_elem = 1;
    }

    if (have_elem &&
	!(type->t & VT_ARRAY) &&
	/* Use i_c_parameter_t, to strip toplevel qualifiers.
	   The source type might have VT_CONSTANT set, which is
	   of course assignable to non-const elements.  */
	is_compatible_unqualified_types(type, &vtop->type)) {
        init_putv(type, sec, c);
    } else if (type->t & VT_ARRAY) {
        s = type->ref;
        n = s->c;
        t1 = pointed_type(type);
        size1 = type_size(t1, &align1);

        no_oblock = 1;
        if ((first && tok != TOK_LSTR && tok != TOK_STR) || 
            tok == '{') {
            if (tok != '{')
                tcc_error(-1, "character array initializer must be a literal, optionally enclosed in braces");
            skip('{');
            no_oblock = 0;
        }

        /* only parse strings here if correct type (otherwise: handle
           them as ((w)char *) expressions */
        if ((tok == TOK_LSTR && 
#ifdef TCC_TARGET_PE
             (t1->t & VT_BTYPE) == VT_SHORT && (t1->t & VT_UNSIGNED)
#else
             (t1->t & VT_BTYPE) == VT_INT
#endif
            ) || (tok == TOK_STR && (t1->t & VT_BTYPE) == VT_BYTE)) {
	    len = 0;
            while (tok == TOK_STR || tok == TOK_LSTR) {
                int cstr_len, ch;

                /* compute maximum number of chars wanted */
                if (tok == TOK_STR)
                    cstr_len = tokc.str.size;
                else
                    cstr_len = tokc.str.size / sizeof(nwchar_t);
                cstr_len--;
                nb = cstr_len;
                if( n >= 0 && nb > ( n - len ))  nb = n - len;
                if( !size_only ) {
                    if( cstr_len > nb )  tcc_error(0, "initializer-string for array is too long");
                    /* in order to go faster for common case (char
                       string in global variable, we handle it
                       specifically */
                    if (sec && tok == TOK_STR && size1 == 1) {
                        if (!NODATA_WANTED)
                            memcpy(sec->data + c + len, tokc.str.data, nb);
                    } else {
                        for(i=0;i<nb;i++) {
                            if (tok == TOK_STR)
                                ch = ((unsigned char *)tokc.str.data)[i];
                            else
                                ch = ((nwchar_t *)tokc.str.data)[i];
			    vpushi(ch);
                            init_putv(t1, sec, c + (len + i) * size1);
                        }
                    }
                }
                len += nb;
                next();
            }
            /* only add trailing zero if enough storage (no
               warning in this case since it is standard) */
            if (n < 0 || len < n) {
                if (!size_only) {
		    vpushi(0);
                    init_putv(t1, sec, c + (len * size1));
                }
                len++;
            }
	    len *= size1;
        } else {
	    indexsym.c = 0;
	    f = &indexsym;

          do_init_list:
	    len = 0;
	    while (tok != '}' || have_elem) {
		len = decl_designator(type, sec, c, &f, size_only, len);
		have_elem = 0;
		if (type->t & VT_ARRAY) {
		    ++indexsym.c;
		    /* special test for multi dimensional arrays (may not
		       be strictly correct if designators are used at the
		       same time) */
		    if (no_oblock && len >= n*size1)
		        break;
		} else {
		    if (s->type.t == VT_UNION)
		        f = NULL;
		    else
		        f = f->next;
		    if (no_oblock && f == NULL)
		        break;
		}

		if (tok == '}')
		    break;
		skip(',');
	    }
        }
        /* put zeros at the end */
	if (!size_only && len < n*size1)
	    init_putz(sec, c + len, n*size1 - len);
        if (!no_oblock)
            skip('}');
        /* patch type size if needed, which happens only for array types */
        if (n < 0)
            s->c = size1 == 1 ? len : ((len + size1 - 1)/size1);
    } else if ((type->t & VT_BTYPE) == VT_STRUCT) {
	size1 = 1;
        no_oblock = 1;
        if (first || tok == '{') {
            skip('{');
            no_oblock = 0;
        }
        s = type->ref;
        f = s->next;
        n = s->c;
	goto do_init_list;
    } else if (tok == '{') {
        next();
        decl_initializer(type, sec, c, first, size_only);
        skip('}');
    } else if (size_only) {
	/* If we supported only ISO C we wouldn't have to accept calling
	   this on anything than an array size_only==1 (and even then
	   only on the outermost level, so no recursion would be needed),
	   because initializing a flex array member isn't supported.
	   But GNU C supports it, so we need to recurse even into
	   subfields of structs and arrays when size_only is set.  */
        /* just skip expression */
        skip_or_save_block(NULL);
    } else {
	if (!have_elem) {
	    /* This should happen only when we haven't parsed
	       the init element above for fear of committing a
	       string constant to memory too early.  */
	    if( tok != TOK_STR && tok != TOK_LSTR )  tcc_error(-1, "string constant expected" );
	    parse_init_elem(!sec ? EXPR_ANY : EXPR_CONST);
	}
        init_putv(type, sec, c);
    }
}

/* parse an initializer for type 't' if 'has_init' is non zero, and
   allocate space in local or global data space ('r' is either
   VT_LOCAL or VT_CONST). If 'v' is non zero, then an associated
   variable 'v' of scope 'scope' is declared before initializers
   are parsed. If 'v' is zero, then a reference to the new object
   is put in the value stack. If 'has_init' is 2, a special parsing
   is done to handle string constants. */
static void decl_initializer_alloc(CType *type, AttributeDef *ad, int r, 
                                   int has_init, int v, int scope)
{
    int size, align, addr;
    TokenString *init_str = NULL;

    Section *sec;
    Sym *flexible_array;
    Sym *sym = NULL;
    int saved_nocode_wanted = nocode_wanted;
#ifdef CONFIG_TCC_BCHECK
    int bcheck = tcc_state->do_bounds_check && !NODATA_WANTED;
#endif

    if (type->t & VT_STATIC) nocode_wanted |= NODATA_WANTED ? 0x40000000 : 0x80000000;

    flexible_array = NULL;
    if ((type->t & VT_BTYPE) == VT_STRUCT) {
        Sym *field = type->ref->next;
        if (field) {
            while (field->next)
                field = field->next;
            if (field->type.t & VT_ARRAY && field->type.ref->c < 0)
                flexible_array = field;
        }
    }

    size = type_size(type, &align);
    /* If unknown size, we must evaluate it before
       evaluating initializers because
       initializers can generate global data too
       (e.g. string pointers or ISOC99 compound
       literals). It also simplifies local
       initializers handling */
    if (size < 0 || (flexible_array && has_init)) {
        if( !has_init ) tcc_error(-1, "unknown type size");
        /* get all init string */
        if (has_init == 2) {
	    init_str = tok_str_alloc();
            /* only get strings */
            while (tok == TOK_STR || tok == TOK_LSTR) {
                tok_str_add_tok(init_str);
                next();
            }
	    tok_str_add(init_str, -1);
	    tok_str_add(init_str, 0);
        } else {
	    skip_or_save_block(&init_str);
        }
        unget_tok(0);

        /* compute size */
        begin_macro(init_str, 1);
        next();
        decl_initializer(type, NULL, 0, 1, 1);
        /* prepare second initializer parsing */
        macro_ptr = init_str->str;
        next();
        
        /* if still unknown size, error */
        size = type_size(type, &align);
        if( size < 0 )  tcc_error(-1, "unknown type size");
    }
    /* If there's a flex member and it was used in the initializer
       adjust size.  */
    if (flexible_array &&
	flexible_array->type.ref->c > 0)
        size += flexible_array->type.ref->c
	        * pointed_size(&flexible_array->type);
    /* take into account specified alignment if bigger */
    if (ad->a.aligned) {
	int speca = 1 << (ad->a.aligned - 1);
        if (speca > align)
            align = speca;
    } else if (ad->a.packed) {
        align = 1;
    }

    if (NODATA_WANTED)
        size = 0, align = 1;

    if ((r & VT_VALMASK) == VT_LOCAL) {
        sec = NULL;
#ifdef CONFIG_TCC_BCHECK
        if (bcheck && (type->t & VT_ARRAY)) {
            loc--;
        }
#endif
        loc = (loc - size) & -align;
        addr = loc;
#ifdef CONFIG_TCC_BCHECK
        /* handles bounds */
        /* XXX: currently, since we do only one pass, we cannot track
           '&' operators, so we add only arrays */
        if (bcheck && (type->t & VT_ARRAY)) {
            addr_t *bounds_ptr;
            /* add padding between regions */
            loc--;
            /* then add local bound info */
            bounds_ptr = section_ptr_add(lbounds_section, 2 * sizeof(addr_t));
            bounds_ptr[0] = addr;
            bounds_ptr[1] = size;
        }
#endif
        if (v) {
            /* local variable */
#ifdef CONFIG_TCC_ASM
	    if (ad->asm_label) {
		int reg = asm_parse_regvar(ad->asm_label);
		if (reg >= 0)
		    r = (r & ~VT_VALMASK) | reg;
	    }
#endif
            sym = sym_push(v, type, r, addr);
            sym->a = ad->a;
        } else {
            /* push local reference */
            vset(type, r, addr);
        }
    } else {
        if (v && scope == VT_CONST) {
            /* see if the symbol was already defined */
            sym = sym_find(v);
            if (sym) {
                patch_storage(sym, ad, type);
                /* we accept several definitions of the same global variable. */
                if (!has_init && sym->c && elfsym(sym)->st_shndx != SHN_UNDEF)
                    goto no_alloc;
            }
        }

        /* allocate symbol in corresponding section */
        sec = ad->section;
        if (!sec) {
            if (has_init)
                sec = data_section;
            else if (tcc_state->nocommon)
                sec = bss_section;
        }

        if (sec) {
	    addr = section_add(sec, size, align);
#ifdef CONFIG_TCC_BCHECK
            /* add padding if bound check */
            if (bcheck)
                section_add(sec, 1, 1);
#endif
        } else {
            addr = align; /* SHN_COMMON is special, symbol value is align */
	    sec = common_section;
        }

        if (v) {
            if (!sym) {
                sym = sym_push(v, type, r | VT_SYM, 0);
                patch_storage(sym, ad, NULL);
            }
            /* Local statics have a scope until now (for
               warnings), remove it here.  */
            sym->sym_scope = 0;
            /* update symbol definition */
	    put_extern_sym(sym, sec, addr, size);
        } else {
            /* push global reference */
            sym = get_sym_ref(type, sec, addr, size);
	    vpushsym(type, sym);
	    vtop->r |= r;
        }

#ifdef CONFIG_TCC_BCHECK
        /* handles bounds now because the symbol must be defined
           before for the relocation */
        if (bcheck) {
            addr_t *bounds_ptr;

            greloca(bounds_section, sym, bounds_section->data_offset, R_DATA_PTR, 0);
            /* then add global bound info */
            bounds_ptr = section_ptr_add(bounds_section, 2 * sizeof(addr_t));
            bounds_ptr[0] = 0; /* relocated */
            bounds_ptr[1] = size;
        }
#endif
    }

    if (type->t & VT_VLA) {
        int a;

        if (NODATA_WANTED)
            goto no_alloc;

        /* save current stack pointer */
        if (vlas_in_scope == 0) {
            if (vla_sp_root_loc == -1)
                vla_sp_root_loc = (loc -= PTR_SIZE);
            gen_vla_sp_save(vla_sp_root_loc);
        }

        vla_runtime_type_size(type, &a);
        gen_vla_alloc(type, a);
#if defined TCC_TARGET_PE && defined TCC_TARGET_X86_64
        /* on _WIN64, because of the function args scratch area, the
           result of alloca differs from RSP and is returned in RAX.  */
        gen_vla_result(addr), addr = (loc -= PTR_SIZE);
#endif
        gen_vla_sp_save(addr);
        vla_sp_loc = addr;
        vlas_in_scope++;

    } else if (has_init) {
	size_t oldreloc_offset = 0;
	if (sec && sec->reloc)
	  oldreloc_offset = sec->reloc->data_offset;
        decl_initializer(type, sec, addr, 1, 0);
	if (sec && sec->reloc)
	  squeeze_multi_relocs(sec, oldreloc_offset);
        /* patch flexible array member size back to -1, */
        /* for possible subsequent similar declarations */
        if (flexible_array)
            flexible_array->type.ref->c = -1;
    }

 no_alloc:
    /* restore parse state if needed */
    if (init_str) {
        end_macro();
        next();
    }

    nocode_wanted = saved_nocode_wanted;
}

/* parse a function defined by symbol 'sym' and generate its code in
   'cur_text_section' */
static void gen_function(Sym *sym)
{
    nocode_wanted = 0;
    ind = cur_text_section->data_offset;
    /* NOTE: we patch the symbol size later */
    put_extern_sym(sym, cur_text_section, ind, 0);
    funcname = get_tok_str(sym->v, NULL);
    func_ind = ind;
    /* Initialize VLA state */
    vla_sp_loc = -1;
    vla_sp_root_loc = -1;
#if defined CONFIG_TCC_GDEBUG
    /* put debug symbol */
    tcc_debug_funcstart(tcc_state, sym);
#endif
    /* push a dummy symbol to enable local sym storage */
    sym_push2(&local_stack, SYM_FIELD, 0, 0);
    local_scope = 1; /* for function parameters */
    gfunc_prolog(&sym->type);
    local_scope = 0;
    rsym = 0;
    block(NULL, NULL, 0);
    nocode_wanted = 0;
    gsym(rsym);
    gfunc_epilog();
    cur_text_section->data_offset = ind;
    label_pop(&global_label_stack, NULL, 0);
    /* reset local stack */
    local_scope = 0;
    sym_pop(&local_stack, NULL, 0);
    /* end of function */
    /* patch symbol size */
    elfsym(sym)->st_size = ind - func_ind;
#if defined CONFIG_TCC_GDEBUG
    tcc_debug_funcend(tcc_state, ind - func_ind);
#endif
    /* It's better to crash than to generate wrong code */
    cur_text_section = NULL;
    funcname = ""; /* for safety */
    func_vt.t = VT_VOID; /* for safety */
    func_var = 0; /* for safety */
    ind = 0; /* for safety */
    nocode_wanted = 0x80000000;
    check_vstack();
}

static void gen_inline_functions(TCCState *s)
{
    Sym *sym;
    int inline_generated, i, ln;
    struct InlineFunc *fn;

    ln = file->line_num;
    /* iterate while inline function are referenced */
    do {
        inline_generated = 0;
        for (i = 0; i < s->nb_inline_fns; ++i) {
            fn = s->inline_fns[i];
            sym = fn->sym;
            if (sym && sym->c) {
                /* the function was used: generate its code and
                   convert it to a normal function */
                fn->sym = NULL;
                if (file)
                    pstrcpy(file->filename, sizeof file->filename, fn->filename);
                sym->type.t &= ~VT_INLINE;

                begin_macro(fn->func_str, 1);
                next();
                cur_text_section = text_section;
                gen_function(sym);
                end_macro();

                inline_generated = 1;
            }
        }
    } while (inline_generated);
    file->line_num = ln;
}

ST_FUNC void free_inline_functions(TCCState *s)
{
    int i;
    /* free tokens of unused inline functions */
    for (i = 0; i < s->nb_inline_fns; ++i) {
        struct InlineFunc *fn = s->inline_fns[i];
        if (fn->sym)
            tok_str_free(fn->func_str);
    }
    dynarray_reset(&s->inline_fns, &s->nb_inline_fns);
}

/* 'l' is VT_LOCAL or VT_CONST to define default storage type, or VT_CMP
   if parsing old style parameter decl list (and FUNC_SYM is set then) */
static int decl0(int l, int is_for_loop_init, Sym *func_sym)
{
    int v, has_init, r;
    CType type, btype;
    Sym *sym;
    AttributeDef ad;

    while (1) {
        if (!parse_btype(&btype, &ad)) {
            if (is_for_loop_init)
                return 0;
            /* skip redundant ';' if not in old parameter decl scope */
            if (tok == ';' && l != VT_CMP) {
                next();
                continue;
            }
            if (l != VT_CONST)
                break;
            if (tok == TOK_ASM1 || tok == TOK_ASM2 || tok == TOK_ASM3) {
                /* global asm block */
                asm_global_instr();
                continue;
            }
            if (tok >= TOK_UIDENT) {
               /* special test for old K&R protos without explicit int
                  type. Only accepted when defining global data */
                btype.t = VT_INT;
            }
            else {
                if( tok != TOK_EOF )  tcc_error(-1, "declaration expected" );
                break;
            }
        }
        if (tok == ';') {
	    if ((btype.t & VT_BTYPE) == VT_STRUCT) {
		int v = btype.ref->v;
		if( !( v & SYM_FIELD ) && ( v & ~SYM_STRUCT ) >= SYM_FIRST_ANOM ) {
        	    tcc_error(0, "unnamed struct/union that defines no instances");
                }
                next();
                continue;
	    }
            if (IS_ENUM(btype.t)) {
                next();
                continue;
            }
        }
        while (1) { /* iterate thru each declaration */
            type = btype;
	    /* If the base type itself was an array type of unspecified
	       size (like in 'typedef int arr[]; arr x = {1};') then
	       we will overwrite the unknown size by the real one for
	       this decl.  We need to unshare the ref symbol holding
	       that size.  */
	    if ((type.t & VT_ARRAY) && type.ref->c < 0) {
		type.ref = sym_push(SYM_FIELD, &type.ref->type, 0, type.ref->c);
	    }
            type_decl(&type, &ad, &v, TYPE_DIRECT);
            if ((type.t & VT_BTYPE) == VT_FUNC) {
                if ((type.t & VT_STATIC) && (l == VT_LOCAL)) {
                    tcc_error(-1, "function without file scope cannot be static");
                }
                /* if old style function prototype, we accept a
                   declaration list */
                sym = type.ref;
                if (sym->f.func_type == FUNC_OLD && l == VT_CONST)
                    decl0(VT_CMP, 0, sym);
            }

            if (gnu_ext && (tok == TOK_ASM1 || tok == TOK_ASM2 || tok == TOK_ASM3)) {
                ad.asm_label = asm_label_instr();
                /* parse one last attribute list, after asm label */
                parse_attribute(&ad);
                if( tok == '{' )  tcc_error(-1, "; expected" );
            }

            if (tok == '{') {
                if( l != VT_CONST )  tcc_error(-1, "cannot use local functions");
                if(( type.t & VT_BTYPE ) != VT_FUNC )  tcc_error(-1, "function definition expected" );

                /* reject abstract declarators in function definition
		   make old style params without decl have int type */
                sym = type.ref;
                while ((sym = sym->next) != NULL) {
                    if( !( sym->v & ~SYM_FIELD ))  tcc_error(-1, "identifier expected" );
		    if( sym->type.t == VT_VOID )  sym->type = int_type;
		}
                
                /* XXX: cannot do better now: convert extern line to static inline */
                if ((type.t & (VT_EXTERN | VT_INLINE)) == (VT_EXTERN | VT_INLINE))
                    type.t = (type.t & ~VT_EXTERN) | VT_STATIC;

                /* put function symbol */
                sym = external_global_sym(v, &type, 0);
                type.t &= ~VT_EXTERN;
                patch_storage(sym, &ad, &type);

                /* static inline functions are just recorded as a kind
                   of macro. Their code will be emitted at the end of
                   the compilation unit only if they are used */
                if ((type.t & (VT_INLINE | VT_STATIC)) == 
                    (VT_INLINE | VT_STATIC)) {
                    struct InlineFunc *fn;
                    const char *filename;
                           
                    filename = file ? file->filename : "";
                    fn = tcc_malloc(sizeof *fn + strlen(filename));
                    strcpy(fn->filename, filename);
                    fn->sym = sym;
		    skip_or_save_block(&fn->func_str);
                    dynarray_add(&tcc_state->inline_fns,
				 &tcc_state->nb_inline_fns, fn);
                } else {
                    /* compute text section */
                    cur_text_section = ad.section;
                    if (!cur_text_section)
                        cur_text_section = text_section;
                    gen_function(sym);
                }
                break;
            } else {
		if (l == VT_CMP) {
		    /* find parameter in function parameter list */
		    for (sym = func_sym->next; sym; sym = sym->next)
			if ((sym->v & ~SYM_FIELD) == v)
			    goto found;
		    tcc_error(-1, "declaration for parameter '%s' but no such parameter", get_tok_str(v, NULL));
found:
		    if (type.t & VT_STORAGE) /* 'register' is okay */
		        tcc_error(-1, "storage class specified for '%s'", get_tok_str(v, NULL));
		    if (sym->type.t != VT_VOID)
		        tcc_error(-1, "redefinition of parameter '%s'", get_tok_str(v, NULL));
		    convert_parameter_type(&type);
		    sym->type = type;
		} else if (type.t & VT_TYPEDEF) {
                    /* save typedefed type  */
                    /* XXX: test storage specifiers ? */
                    sym = sym_find(v);
                    if (sym && sym->sym_scope == local_scope) {
                        if (!is_compatible_types(&sym->type, &type)
                            || !(sym->type.t & VT_TYPEDEF))
                            tcc_error(-1, "incompatible redefinition of '%s'", get_tok_str(v, NULL));
                        sym->type = type;
                    } else {
                        sym = sym_push(v, &type, 0, 0);
                    }
                    sym->a = ad.a;
                    sym->f = ad.f;
                } else {
                    r = 0;
                    if ((type.t & VT_BTYPE) == VT_FUNC) {
                        /* external function definition */
                        /* specific case for func_call attribute */
                        type.ref->f = ad.f;
                    } else if (!(type.t & VT_ARRAY)) {
                        /* not lvalue if array */
                        r |= lvalue_type(type.t);
                    }
                    has_init = (tok == '=');
                    if (has_init && (type.t & VT_VLA))
                        tcc_error(-1, "variable length array cannot be initialized");
                    if (((type.t & VT_EXTERN) && (!has_init || l != VT_CONST)) ||
			((type.t & VT_BTYPE) == VT_FUNC) ||
                        ((type.t & VT_ARRAY) && (type.t & VT_STATIC) &&
                         !has_init && l == VT_CONST && type.ref->c < 0)) {
                        /* external variable or function */
                        /* NOTE: as GCC, uninitialized global static
                           arrays of null size are considered as
                           extern */
                        type.t |= VT_EXTERN;
                        sym = external_sym(v, &type, r, &ad);
                        if (ad.alias_target) {
                            ElfSym *esym;
                            Sym *alias_target;
                            alias_target = sym_find(ad.alias_target);
                            esym = elfsym(alias_target);
                            if( !esym )  tcc_error(-1, "unsupported forward __alias__ attribute");
                            /* Local statics have a scope until now (for
                               warnings), remove it here.  */
                            sym->sym_scope = 0;
                            put_extern_sym2(sym, esym->st_shndx, esym->st_value, esym->st_size, 0);
                        }
                    } else {
                        if (type.t & VT_STATIC)
                            r |= VT_CONST;
                        else
                            r |= l;
                        if (has_init)
                            next();
                        else if (l == VT_CONST)
                            /* uninitialized global variables may be overridden */
                            type.t |= VT_EXTERN;
                        decl_initializer_alloc(&type, &ad, r, has_init, v, l);
                    }
                }
                if (tok != ',') {
                    if (is_for_loop_init)
                        return 1;
                    skip(';');
                    break;
                }
                next();
            }
            ad.a.aligned = 0;
        }
    }
    return 0;
}

static void decl(int l)
{
    decl0(l, 0, NULL);
}

/* ------------------------------------------------------------------------- */

/*  ELF file handling for TCC
 *  Copyright (c) 2001-2004 Fabrice Bellard
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */

/* Define this to get some debug output during relocation processing.  */
#undef DEBUG_RELOC

/********************************************************/
/* global variables */

ST_DATA Section *text_section, *data_section, *bss_section; /* predefined sections */
ST_DATA Section *common_section;
ST_DATA Section *cur_text_section; /* current section where function code is generated */
#ifdef CONFIG_TCC_ASM
ST_DATA Section *last_text_section; /* to handle .previous asm directive */
#endif
#ifdef CONFIG_TCC_BCHECK
/* bound check related sections */
ST_DATA Section *bounds_section; /* contains global data bound description */
ST_DATA Section *lbounds_section; /* contains local data bound description */
#endif
/* symbol sections */
ST_DATA Section *symtab_section;
/* debug sections */
ST_DATA Section *stab_section, *stabstr_section;

/* XXX: avoid static variable */
static int new_undef_sym = 0; /* Is there a new undefined sym since last new_undef_sym() */

/* special flag to indicate that the section should not be linked to the other ones */
#define SHF_PRIVATE 0x80000000
/* section is dynsymtab_section */
#define SHF_DYNSYM 0x40000000

/* ------------------------------------------------------------------------- */

ST_FUNC void tccelf_new(TCCState *s)
{
    /* no section zero */
    dynarray_add(&s->sections, &s->nb_sections, NULL);

    /* create standard sections */
    text_section = new_section(s, ".text", SHT_PROGBITS, SHF_ALLOC | SHF_EXECINSTR);
    data_section = new_section(s, ".data", SHT_PROGBITS, SHF_ALLOC | SHF_WRITE);
    bss_section = new_section(s, ".bss", SHT_NOBITS, SHF_ALLOC | SHF_WRITE);
    common_section = new_section(s, ".common", SHT_NOBITS, SHF_PRIVATE);
    common_section->sh_num = SHN_COMMON;

    /* symbols are always generated for linking stage */
    symtab_section = new_symtab(s, ".symtab", SHT_SYMTAB, 0,
                                ".strtab",
                                ".hashtab", SHF_PRIVATE);
    s->symtab = symtab_section;

    /* private symbol table for dynamic symbols */
    s->dynsymtab_section = new_symtab(s, ".dynsymtab", SHT_SYMTAB, SHF_PRIVATE|SHF_DYNSYM,
                                      ".dynstrtab",
                                      ".dynhashtab", SHF_PRIVATE);
    get_sym_attr(s, 0, 1);
}

#ifdef CONFIG_TCC_BCHECK
ST_FUNC void tccelf_bounds_new(TCCState *s)
{
    /* create bounds sections */
    bounds_section = new_section(s, ".bounds",
                                 SHT_PROGBITS, SHF_ALLOC);
    lbounds_section = new_section(s, ".lbounds",
                                  SHT_PROGBITS, SHF_ALLOC);
}
#endif

#if defined CONFIG_TCC_GDEBUG
ST_FUNC void tccelf_stab_new(TCCState *s)
{
    stab_section = new_section(s, ".stab", SHT_PROGBITS, 0);
    stab_section->sh_entsize = sizeof(Stab_Sym);
    stabstr_section = new_section(s, ".stabstr", SHT_STRTAB, 0);
    put_elf_str(stabstr_section, "");
    stab_section->link = stabstr_section;
    /* put first entry */
    put_stabs("", 0, 0, 0, 0);
}
#endif

static void free_section(Section *s)
{
    tcc_free(s->data);
}

ST_FUNC void tccelf_delete(TCCState *s1)
{
    int i;

    /* free all sections */
    for(i = 1; i < s1->nb_sections; i++)
        free_section(s1->sections[i]);
    dynarray_reset(&s1->sections, &s1->nb_sections);

    for(i = 0; i < s1->nb_priv_sections; i++)
        free_section(s1->priv_sections[i]);
    dynarray_reset(&s1->priv_sections, &s1->nb_priv_sections);

    /* free any loaded DLLs */
#ifdef TCC_IS_NATIVE
    for ( i = 0; i < s1->nb_loaded_dlls; i++) {
        DLLReference *ref = s1->loaded_dlls[i];
        if ( ref->handle )
            dlclose(ref->handle);
    }
#endif
    /* free loaded dlls array */
    dynarray_reset(&s1->loaded_dlls, &s1->nb_loaded_dlls);
    tcc_free(s1->sym_attrs);

    symtab_section = NULL; /* for tccrun.c:rt_printline() */
}

/* save section data state */
ST_FUNC void tccelf_begin_file(TCCState *s1)
{
    Section *s; int i;
    for (i = 1; i < s1->nb_sections; i++) {
        s = s1->sections[i];
        s->sh_offset = s->data_offset;
    }
    /* disable symbol hashing during compilation */
    s = s1->symtab, s->reloc = s->hash, s->hash = NULL;
#if defined TCC_TARGET_X86_64 && defined TCC_TARGET_PE
    s1->uw_sym = 0;
#endif
}

/* At the end of compilation, convert any UNDEF syms to global, and merge
   with previously existing symbols */
ST_FUNC void tccelf_end_file(TCCState *s1)
{
    Section *s = s1->symtab;
    int first_sym, nb_syms, *tr, i;

    first_sym = s->sh_offset / sizeof (ElfSym);
    nb_syms = s->data_offset / sizeof (ElfSym) - first_sym;
    s->data_offset = s->sh_offset;
    s->link->data_offset = s->link->sh_offset;
    s->hash = s->reloc, s->reloc = NULL;
    tr = tcc_mallocz(nb_syms * sizeof *tr);

    for (i = 0; i < nb_syms; ++i) {
        ElfSym *sym = (ElfSym*)s->data + first_sym + i;
        if (sym->st_shndx == SHN_UNDEF
            && ELFW(ST_BIND)(sym->st_info) == STB_LOCAL)
            sym->st_info = ELFW(ST_INFO)(STB_GLOBAL, ELFW(ST_TYPE)(sym->st_info));
        tr[i] = set_elf_sym(s, sym->st_value, sym->st_size, sym->st_info,
            sym->st_other, sym->st_shndx, s->link->data + sym->st_name);
    }
    /* now update relocations */
    for (i = 1; i < s1->nb_sections; i++) {
        Section *sr = s1->sections[i];
        if (sr->sh_type == SHT_RELX && sr->link == s) {
            ElfW_Rel *rel = (ElfW_Rel*)(sr->data + sr->sh_offset);
            ElfW_Rel *rel_end = (ElfW_Rel*)(sr->data + sr->data_offset);
            for (; rel < rel_end; ++rel) {
                int n = ELFW(R_SYM)(rel->r_info) - first_sym;
                //if (n < 0) tcc_error(-1, "internal: invalid symbol index in relocation");
                rel->r_info = ELFW(R_INFO)(tr[n], ELFW(R_TYPE)(rel->r_info));
            }
        }
    }
    tcc_free(tr);
}

ST_FUNC Section *new_section(TCCState *s1, const char *name, int sh_type, int sh_flags)
{
    Section *sec;

    sec = tcc_mallocz(sizeof(Section) + strlen(name));
    strcpy(sec->name, name);
    sec->sh_type = sh_type;
    sec->sh_flags = sh_flags;
    switch(sh_type) {
    case SHT_HASH:
    case SHT_REL:
    case SHT_RELA:
    case SHT_DYNSYM:
    case SHT_SYMTAB:
    case SHT_DYNAMIC:
        sec->sh_addralign = 4;
        break;
    case SHT_STRTAB:
        sec->sh_addralign = 1;
        break;
    default:
        sec->sh_addralign =  PTR_SIZE; /* gcc/pcc default alignment */
        break;
    }

    if (sh_flags & SHF_PRIVATE) {
        dynarray_add(&s1->priv_sections, &s1->nb_priv_sections, sec);
    } else {
        sec->sh_num = s1->nb_sections;
        dynarray_add(&s1->sections, &s1->nb_sections, sec);
    }

    return sec;
}

ST_FUNC Section *new_symtab(TCCState *s1,
                           const char *symtab_name, int sh_type, int sh_flags,
                           const char *strtab_name,
                           const char *hash_name, int hash_sh_flags)
{
    Section *symtab, *strtab, *hash;
    int *ptr, nb_buckets;

    symtab = new_section(s1, symtab_name, sh_type, sh_flags);
    symtab->sh_entsize = sizeof(ElfW(Sym));
    strtab = new_section(s1, strtab_name, SHT_STRTAB, sh_flags);
    put_elf_str(strtab, "");
    symtab->link = strtab;
    put_elf_sym(symtab, 0, 0, 0, 0, 0, NULL);

    nb_buckets = 1;

    hash = new_section(s1, hash_name, SHT_HASH, hash_sh_flags);
    hash->sh_entsize = sizeof(int);
    symtab->hash = hash;
    hash->link = symtab;

    ptr = section_ptr_add(hash, (2 + nb_buckets + 1) * sizeof(int));
    ptr[0] = nb_buckets;
    ptr[1] = 1;
    memset(ptr + 2, 0, (nb_buckets + 1) * sizeof(int));
    return symtab;
}

/* realloc section and set its content to zero */
ST_FUNC void section_realloc(Section *sec, unsigned long new_size)
{
    unsigned long size;
    unsigned char *data;

    size = sec->data_allocated;
    if (size == 0)
        size = 1;
    while (size < new_size)
        size = size * 2;
    data = tcc_realloc(sec->data, size);
    memset(data + sec->data_allocated, 0, size - sec->data_allocated);
    sec->data = data;
    sec->data_allocated = size;
}

/* reserve at least 'size' bytes aligned per 'align' in section
   'sec' from current offset, and return the aligned offset */
ST_FUNC size_t section_add(Section *sec, addr_t size, int align)
{
    size_t offset, offset1;

    offset = (sec->data_offset + align - 1) & -align;
    offset1 = offset + size;
    if (sec->sh_type != SHT_NOBITS && offset1 > sec->data_allocated)
        section_realloc(sec, offset1);
    sec->data_offset = offset1;
    if (align > sec->sh_addralign)
        sec->sh_addralign = align;
    return offset;
}

/* reserve at least 'size' bytes in section 'sec' from
   sec->data_offset. */
ST_FUNC void *section_ptr_add(Section *sec, addr_t size)
{
    size_t offset = section_add(sec, size, 1);
    return sec->data + offset;
}

/* reserve at least 'size' bytes from section start */
ST_FUNC void section_reserve(Section *sec, unsigned long size)
{
    if (size > sec->data_allocated)
        section_realloc(sec, size);
    if (size > sec->data_offset)
        sec->data_offset = size;
}

/* return a reference to a section, and create it if it does not
   exists */
ST_FUNC Section *find_section(TCCState *s1, const char *name)
{
    Section *sec;
    int i;
    for(i = 1; i < s1->nb_sections; i++) {
        sec = s1->sections[i];
        if (!strcmp(name, sec->name))
            return sec;
    }
    /* sections are created as PROGBITS */
    return new_section(s1, name, SHT_PROGBITS, SHF_ALLOC);
}

/* ------------------------------------------------------------------------- */

ST_FUNC int put_elf_str(Section *s, const char *sym)
{
    int offset, len;
    char *ptr;

    len = strlen(sym) + 1;
    offset = s->data_offset;
    ptr = section_ptr_add(s, len);
    memmove(ptr, sym, len);
    return offset;
}

/* elf symbol hashing function */
static unsigned long elf_hash(const unsigned char *name)
{
    unsigned long h = 0, g;

    while (*name) {
        h = (h << 4) + *name++;
        g = h & 0xf0000000;
        if (g)
            h ^= g >> 24;
        h &= ~g;
    }
    return h;
}

/* rebuild hash table of section s */
/* NOTE: we do factorize the hash table code to go faster */
static void rebuild_hash(Section *s, unsigned int nb_buckets)
{
    ElfW(Sym) *sym;
    int *ptr, *hash, nb_syms, sym_index, h;
    unsigned char *strtab;

    strtab = s->link->data;
    nb_syms = s->data_offset / sizeof(ElfW(Sym));

    if (!nb_buckets)
        nb_buckets = ((int*)s->hash->data)[0];

    s->hash->data_offset = 0;
    ptr = section_ptr_add(s->hash, (2 + nb_buckets + nb_syms) * sizeof(int));
    ptr[0] = nb_buckets;
    ptr[1] = nb_syms;
    ptr += 2;
    hash = ptr;
    memset(hash, 0, (nb_buckets + 1) * sizeof(int));
    ptr += nb_buckets + 1;

    sym = (ElfW(Sym) *)s->data + 1;
    for(sym_index = 1; sym_index < nb_syms; sym_index++) {
        if (ELFW(ST_BIND)(sym->st_info) != STB_LOCAL) {
            h = elf_hash(strtab + sym->st_name) % nb_buckets;
            *ptr = hash[h];
            hash[h] = sym_index;
        } else {
            *ptr = 0;
        }
        ptr++;
        sym++;
    }
}

/* return the symbol number */
ST_FUNC int put_elf_sym(Section *s, addr_t value, unsigned long size,
    int info, int other, int shndx, const char *name)
{
    int name_offset, sym_index;
    int nbuckets, h;
    ElfW(Sym) *sym;
    Section *hs;

    sym = section_ptr_add(s, sizeof(ElfW(Sym)));
    if (name && name[0])
        name_offset = put_elf_str(s->link, name);
    else
        name_offset = 0;
    /* XXX: endianness */
    sym->st_name = name_offset;
    sym->st_value = value;
    sym->st_size = size;
    sym->st_info = info;
    sym->st_other = other;
    sym->st_shndx = shndx;
    sym_index = sym - (ElfW(Sym) *)s->data;
    hs = s->hash;
    if (hs) {
        int *ptr, *base;
        ptr = section_ptr_add(hs, sizeof(int));
        base = (int *)hs->data;
        /* only add global or weak symbols. */
        if (ELFW(ST_BIND)(info) != STB_LOCAL) {
            /* add another hashing entry */
            nbuckets = base[0];
            h = elf_hash((unsigned char *)s->link->data + name_offset) % nbuckets;
            *ptr = base[2 + h];
            base[2 + h] = sym_index;
            base[1]++;
            /* we resize the hash table */
            hs->nb_hashed_syms++;
            if (hs->nb_hashed_syms > 2 * nbuckets) {
                rebuild_hash(s, 2 * nbuckets);
            }
        } else {
            *ptr = 0;
            base[1]++;
        }
    }
    return sym_index;
}

ST_FUNC int find_elf_sym(Section *s, const char *name)
{
    ElfW(Sym) *sym;
    Section *hs;
    int nbuckets, sym_index, h;
    const char *name1;

    hs = s->hash;
    if (!hs)
        return 0;
    nbuckets = ((int *)hs->data)[0];
    h = elf_hash((unsigned char *) name) % nbuckets;
    sym_index = ((int *)hs->data)[2 + h];
    while (sym_index != 0) {
        sym = &((ElfW(Sym) *)s->data)[sym_index];
        name1 = (char *) s->link->data + sym->st_name;
        if (!strcmp(name, name1))
            return sym_index;
        sym_index = ((int *)hs->data)[2 + nbuckets + sym_index];
    }
    return 0;
}

/* return elf symbol value, signal error if 'err' is nonzero */
ST_FUNC addr_t get_elf_sym_addr(TCCState *s, const char *name, int err)
{
    int sym_index;
    ElfW(Sym) *sym;

    sym_index = find_elf_sym(s->symtab, name);
    sym = &((ElfW(Sym) *)s->symtab->data)[sym_index];
    if (!sym_index || sym->st_shndx == SHN_UNDEF) {
        if( err )  tcc_error(-1, "%s not defined", name);
        return 0;
    }
    return sym->st_value;
}

/* return elf symbol value */
LIBTCCAPI void *tcc_get_symbol(TCCState *s, const char *name)
{
    return (void*)(uintptr_t)get_elf_sym_addr(s, name, 0);
}

#if defined TCC_IS_NATIVE || defined TCC_TARGET_PE
/* return elf symbol value or error */
ST_FUNC void* tcc_get_symbol_err(TCCState *s, const char *name)
{
    return (void*)(uintptr_t)get_elf_sym_addr(s, name, 1);
}
#endif

/* add an elf symbol : check if it is already defined and patch
   it. Return symbol index. NOTE that sh_num can be SHN_UNDEF. */
ST_FUNC int set_elf_sym(Section *s, addr_t value, unsigned long size,
                       int info, int other, int shndx, const char *name)
{
    ElfW(Sym) *esym;
    int sym_bind, sym_index, sym_type, esym_bind;
    unsigned char sym_vis, esym_vis, new_vis;

    sym_bind = ELFW(ST_BIND)(info);
    sym_type = ELFW(ST_TYPE)(info);
    sym_vis = ELFW(ST_VISIBILITY)(other);

    if (sym_bind != STB_LOCAL) {
        /* we search global or weak symbols */
        sym_index = find_elf_sym(s, name);
        if (!sym_index)
            goto do_def;
        esym = &((ElfW(Sym) *)s->data)[sym_index];
        if (esym->st_value == value && esym->st_size == size && esym->st_info == info
            && esym->st_other == other && esym->st_shndx == shndx)
            return sym_index;
        if (esym->st_shndx != SHN_UNDEF) {
            esym_bind = ELFW(ST_BIND)(esym->st_info);
            /* propagate the most constraining visibility */
            /* STV_DEFAULT(0)<STV_PROTECTED(3)<STV_HIDDEN(2)<STV_INTERNAL(1) */
            esym_vis = ELFW(ST_VISIBILITY)(esym->st_other);
            if (esym_vis == STV_DEFAULT) {
                new_vis = sym_vis;
            } else if (sym_vis == STV_DEFAULT) {
                new_vis = esym_vis;
            } else {
                new_vis = (esym_vis < sym_vis) ? esym_vis : sym_vis;
            }
            esym->st_other = (esym->st_other & ~ELFW(ST_VISIBILITY)(-1))
                             | new_vis;
            other = esym->st_other; /* in case we have to patch esym */
            if (shndx == SHN_UNDEF) {
                /* ignore adding of undefined symbol if the
                   corresponding symbol is already defined */
            } else if (sym_bind == STB_GLOBAL && esym_bind == STB_WEAK) {
                /* global overrides weak, so patch */
                goto do_patch;
            } else if (sym_bind == STB_WEAK && esym_bind == STB_GLOBAL) {
                /* weak is ignored if already global */
            } else if (sym_bind == STB_WEAK && esym_bind == STB_WEAK) {
                /* keep first-found weak definition, ignore subsequents */
            } else if (sym_vis == STV_HIDDEN || sym_vis == STV_INTERNAL) {
                /* ignore hidden symbols after */
            } else if ((esym->st_shndx == SHN_COMMON
                            || esym->st_shndx == bss_section->sh_num)
                        && (shndx < SHN_LORESERVE
                            && shndx != bss_section->sh_num)) {
                /* data symbol gets precedence over common/bss */
                goto do_patch;
            } else if (shndx == SHN_COMMON || shndx == bss_section->sh_num) {
                /* data symbol keeps precedence over common/bss */
            } else if (s->sh_flags & SHF_DYNSYM) {
                /* we accept that two DLL define the same symbol */
	    } else if (esym->st_other & ST_ASM_SET) {
		/* If the existing symbol came from an asm .set
		   we can override.  */
		goto do_patch;
            }
            else  tcc_error(1, "'%s' defined twice", name);
        }
        else {
        do_patch:
            esym->st_info = ELFW(ST_INFO)(sym_bind, sym_type);
            esym->st_shndx = shndx;
            new_undef_sym = 1;
            esym->st_value = value;
            esym->st_size = size;
            esym->st_other = other;
        }
    } else {
    do_def:
        sym_index = put_elf_sym(s, value, size,
                                ELFW(ST_INFO)(sym_bind, sym_type), other,
                                shndx, name);
    }
    return sym_index;
}

/* put relocation */
ST_FUNC void put_elf_reloca(Section *symtab, Section *s, unsigned long offset,
                            int type, int symbol, addr_t addend)
{
    char buf[256];
    Section *sr;
    ElfW_Rel *rel;

    sr = s->reloc;
    if (!sr) {
        /* if no relocation section, create it */
        snprintf(buf, sizeof(buf), REL_SECTION_FMT, s->name);
        /* if the symtab is allocated, then we consider the relocation
           are also */
        sr = new_section(tcc_state, buf, SHT_RELX, symtab->sh_flags);
        sr->sh_entsize = sizeof(ElfW_Rel);
        sr->link = symtab;
        sr->sh_info = s->sh_num;
        s->reloc = sr;
    }
    rel = section_ptr_add(sr, sizeof(ElfW_Rel));
    rel->r_offset = offset;
    rel->r_info = ELFW(R_INFO)(symbol, type);
#if SHT_RELX == SHT_RELA
    rel->r_addend = addend;
#else
    if( addend )  tcc_error(-1, "non-zero addend on REL architecture");
#endif
}

ST_FUNC void put_elf_reloc(Section *symtab, Section *s, unsigned long offset,
                           int type, int symbol)
{
    put_elf_reloca(symtab, s, offset, type, symbol, 0);
}

/* Remove relocations for section S->reloc starting at oldrelocoffset
   that are to the same place, retaining the last of them.  As side effect
   the relocations are sorted.  Possibly reduces the number of relocs.  */
ST_FUNC void squeeze_multi_relocs(Section *s, size_t oldrelocoffset)
{
    Section *sr = s->reloc;
    ElfW_Rel *r, *dest;
    ssize_t a;
    ElfW(Addr) addr;

    if (oldrelocoffset + sizeof(*r) >= sr->data_offset)
      return;
    /* The relocs we're dealing with are the result of initializer parsing.
       So they will be mostly in order and there aren't many of them.
       Secondly we need a stable sort (which qsort isn't).  We use
       a simple insertion sort.  */
    for (a = oldrelocoffset + sizeof(*r); a < sr->data_offset; a += sizeof(*r)) {
	ssize_t i = a - sizeof(*r);
	addr = ((ElfW_Rel*)(sr->data + a))->r_offset;
	for (; i >= (ssize_t)oldrelocoffset &&
	       ((ElfW_Rel*)(sr->data + i))->r_offset > addr; i -= sizeof(*r)) {
	    ElfW_Rel tmp = *(ElfW_Rel*)(sr->data + a);
	    *(ElfW_Rel*)(sr->data + a) = *(ElfW_Rel*)(sr->data + i);
	    *(ElfW_Rel*)(sr->data + i) = tmp;
	}
    }

    r = (ElfW_Rel*)(sr->data + oldrelocoffset);
    dest = r;
    for (; r < (ElfW_Rel*)(sr->data + sr->data_offset); r++) {
	if (dest->r_offset != r->r_offset)
	  dest++;
	*dest = *r;
    }
    sr->data_offset = (unsigned char*)dest - sr->data + sizeof(*r);
}


/* put stab debug information */
#if defined CONFIG_TCC_GDEBUG
ST_FUNC void put_stabs(const char *str, int type, int other, int desc, unsigned long value)
{
    Stab_Sym *sym;

    sym = section_ptr_add(stab_section, sizeof(Stab_Sym));
    if (str) {
        sym->n_strx = put_elf_str(stabstr_section, str);
    } else {
        sym->n_strx = 0;
    }
    sym->n_type = type;
    sym->n_other = other;
    sym->n_desc = desc;
    sym->n_value = value;
}
ST_FUNC void put_stabs_r(const char *str, int type, int other, int desc,
                        unsigned long value, Section *sec, int sym_index)
{
    put_stabs(str, type, other, desc, value);
    put_elf_reloc(symtab_section, stab_section,
                  stab_section->data_offset - sizeof(unsigned int),
                  R_DATA_32, sym_index);
}
ST_FUNC void put_stabn(int type, int other, int desc, int value)
{
    put_stabs(NULL, type, other, desc, value);
}
ST_FUNC void put_stabd(int type, int other, int desc)
{
    put_stabs(NULL, type, other, desc, 0);
}
#endif  /**  #if defined CONFIG_TCC_GDEBUG  **/


ST_FUNC struct sym_attr *get_sym_attr(TCCState *s1, int index, int alloc)
{
    int n;
    struct sym_attr *tab;

    if (index >= s1->nb_sym_attrs) {
        if (!alloc)
            return s1->sym_attrs;
        /* find immediately bigger power of 2 and reallocate array */
        n = 1;
        while (index >= n)
            n *= 2;
        tab = tcc_realloc(s1->sym_attrs, n * sizeof(*s1->sym_attrs));
        s1->sym_attrs = tab;
        memset(s1->sym_attrs + s1->nb_sym_attrs, 0,
               (n - s1->nb_sym_attrs) * sizeof(*s1->sym_attrs));
        s1->nb_sym_attrs = n;
    }
    return &s1->sym_attrs[index];
}

/* Browse each elem of type <type> in section <sec> starting at elem <startoff>
   using variable <elem> */
#define for_each_elem(sec, startoff, elem, type) \
    for (elem = (type *) sec->data + startoff; \
         elem < (type *) (sec->data + sec->data_offset); elem++)

/* In an ELF file symbol table, the local symbols must appear below
   the global and weak ones. Since TCC cannot sort it while generating
   the code, we must do it after. All the relocation tables are also
   modified to take into account the symbol table sorting */
static void sort_syms(TCCState *s1, Section *s)
{
    int *old_to_new_syms;
    ElfW(Sym) *new_syms;
    int nb_syms, i;
    ElfW(Sym) *p, *q;
    ElfW_Rel *rel;
    Section *sr;
    int type, sym_index;

    nb_syms = s->data_offset / sizeof(ElfW(Sym));
    new_syms = tcc_malloc(nb_syms * sizeof(ElfW(Sym)));
    old_to_new_syms = tcc_malloc(nb_syms * sizeof(int));

    /* first pass for local symbols */
    p = (ElfW(Sym) *)s->data;
    q = new_syms;
    for(i = 0; i < nb_syms; i++) {
        if (ELFW(ST_BIND)(p->st_info) == STB_LOCAL) {
            old_to_new_syms[i] = q - new_syms;
            *q++ = *p;
        }
        p++;
    }
    /* save the number of local symbols in section header */
    if( s->sh_size )    /* this 'if' makes IDA happy */
        s->sh_info = q - new_syms;

    /* then second pass for non local symbols */
    p = (ElfW(Sym) *)s->data;
    for(i = 0; i < nb_syms; i++) {
        if (ELFW(ST_BIND)(p->st_info) != STB_LOCAL) {
            old_to_new_syms[i] = q - new_syms;
            *q++ = *p;
        }
        p++;
    }

    /* we copy the new symbols to the old */
    memcpy(s->data, new_syms, nb_syms * sizeof(ElfW(Sym)));
    tcc_free(new_syms);

    /* now we modify all the relocations */
    for(i = 1; i < s1->nb_sections; i++) {
        sr = s1->sections[i];
        if (sr->sh_type == SHT_RELX && sr->link == s) {
            for_each_elem(sr, 0, rel, ElfW_Rel) {
                sym_index = ELFW(R_SYM)(rel->r_info);
                type = ELFW(R_TYPE)(rel->r_info);
                sym_index = old_to_new_syms[sym_index];
                rel->r_info = ELFW(R_INFO)(sym_index, type);
            }
        }
    }

    tcc_free(old_to_new_syms);
}

/* relocate symbol table, resolve undefined symbols if do_resolve is
   true and output error if undefined symbol. */
ST_FUNC void relocate_syms(TCCState *s1, Section *symtab, int do_resolve)
{
    ElfW(Sym) *sym;
    int sym_bind, sh_num;
    const char *name;

    for_each_elem(symtab, 1, sym, ElfW(Sym)) {
        sh_num = sym->st_shndx;
        if (sh_num == SHN_UNDEF) {
            name = (char *) s1->symtab->link->data + sym->st_name;
            /* Use ld.so to resolve symbol for us (for tcc -run) */
            if (do_resolve) {
#if defined TCC_IS_NATIVE && !defined TCC_TARGET_PE
                void *addr = dlsym(RTLD_DEFAULT, name);
                if (addr) {
                    sym->st_value = (addr_t) addr;
#ifdef DEBUG_RELOC
		    printf ("relocate_sym: %s -> 0x%lx\n", name, sym->st_value);
#endif
                    goto found;
                }
#endif
            /* if dynamic symbol exist, it will be used in relocate_section */
            } else if (s1->dynsym && find_elf_sym(s1->dynsym, name))
                goto found;
            /* XXX: _fp_hw seems to be part of the ABI, so we ignore
               it */
            if (!strcmp(name, "_fp_hw"))
                goto found;
            /* only weak symbols are accepted to be undefined. Their
               value is zero */
            sym_bind = ELFW(ST_BIND)(sym->st_info);
            if (sym_bind == STB_WEAK)
                sym->st_value = 0;
            else  tcc_error(1, "undefined symbol '%s'", name);
        } else if (sh_num < SHN_LORESERVE) {
            /* add section base */
            sym->st_value += s1->sections[sym->st_shndx]->sh_addr;
        }
    found: ;
    }
}

/* relocate a given section (CPU dependent) by applying the relocations
   in the associated relocation section */
ST_FUNC void relocate_section(TCCState *s1, Section *s)
{
    Section *sr = s->reloc;
    ElfW_Rel *rel;
    ElfW(Sym) *sym;
    int type, sym_index;
    unsigned char *ptr;
    addr_t tgt, addr;

    relocate_init(sr);

    for_each_elem(sr, 0, rel, ElfW_Rel) {
        ptr = s->data + rel->r_offset;
        sym_index = ELFW(R_SYM)(rel->r_info);
        sym = &((ElfW(Sym) *)symtab_section->data)[sym_index];
        type = ELFW(R_TYPE)(rel->r_info);
        tgt = sym->st_value;
#if SHT_RELX == SHT_RELA
        tgt += rel->r_addend;
#endif
        addr = s->sh_addr + rel->r_offset;
        relocate(s1, rel, type, ptr, addr, tgt);
    }
    /* if the relocation is allocated, we change its symbol table */
    if (sr->sh_flags & SHF_ALLOC)
        sr->link = s1->dynsym;
}

/* relocate relocation table in 'sr' */
static void relocate_rel(TCCState *s1, Section *sr)
{
    Section *s;
    ElfW_Rel *rel;

    s = s1->sections[sr->sh_info];
    for_each_elem(sr, 0, rel, ElfW_Rel)
        rel->r_offset += s->sh_addr;
}

/* count the number of dynamic relocations so that we can reserve
   their space */
static int prepare_dynamic_rel(TCCState *s1, Section *sr)
{
    ElfW_Rel *rel;
    int sym_index, type, count;

    count = 0;
    for_each_elem(sr, 0, rel, ElfW_Rel) {
        sym_index = ELFW(R_SYM)(rel->r_info);
        type = ELFW(R_TYPE)(rel->r_info);
        switch(type) {
#if defined(TCC_TARGET_I386)
        case R_386_32:
            if (!get_sym_attr(s1, sym_index, 0)->dyn_index
                && ((ElfW(Sym)*)symtab_section->data + sym_index)->st_shndx == SHN_UNDEF) {
                /* don't fixup unresolved (weak) symbols */
                rel->r_info = ELFW(R_INFO)(sym_index, R_386_RELATIVE);
                break;
            }
#elif defined(TCC_TARGET_X86_64)
        case R_X86_64_32:
        case R_X86_64_32S:
        case R_X86_64_64:
#endif
            count++;
            break;
#if defined(TCC_TARGET_I386)
        case R_386_PC32:
#elif defined(TCC_TARGET_X86_64)
        case R_X86_64_PC32:
#endif
            if (get_sym_attr(s1, sym_index, 0)->dyn_index)
                count++;
            break;
        default:
            break;
        }
    }
    if (count) {
        /* allocate the section */
        sr->sh_flags |= SHF_ALLOC;
        sr->sh_size = count * sizeof(ElfW_Rel);
    }
    return count;
}

static void build_got(TCCState *s1)
{
    /* if no got, then create it */
    s1->got = new_section(s1, ".got", SHT_PROGBITS, SHF_ALLOC | SHF_WRITE);
    s1->got->sh_entsize = 4;
    set_elf_sym(symtab_section, 0, 4, ELFW(ST_INFO)(STB_GLOBAL, STT_OBJECT),
                0, s1->got->sh_num, "_GLOBAL_OFFSET_TABLE_");
    /* keep space for _DYNAMIC pointer and two dummy got entries */
    section_ptr_add(s1->got, 3 * PTR_SIZE);
}

/* Create a GOT and (for function call) a PLT entry corresponding to a symbol
   in s1->symtab. When creating the dynamic symbol table entry for the GOT
   relocation, use 'size' and 'info' for the corresponding symbol metadata.
   Returns the offset of the GOT or (if any) PLT entry. */
static struct sym_attr * put_got_entry(TCCState *s1, int dyn_reloc_type,
                                       unsigned long size,
                                       int info, int sym_index)
{
    int need_plt_entry;
    const char *name;
    ElfW(Sym) *sym;
    struct sym_attr *attr;
    unsigned got_offset;
    char plt_name[100];
    int len;

    need_plt_entry = (dyn_reloc_type == R_JMP_SLOT);
    attr = get_sym_attr(s1, sym_index, 1);

    /* In case a function is both called and its address taken 2 GOT entries
       are created, one for taking the address (GOT) and the other for the PLT
       entry (PLTGOT).  */
    if (need_plt_entry ? attr->plt_offset : attr->got_offset)
        return attr;

    /* create the GOT entry */
    got_offset = s1->got->data_offset;
    section_ptr_add(s1->got, PTR_SIZE);

    /* Create the GOT relocation that will insert the address of the object or
       function of interest in the GOT entry. This is a static relocation for
       memory output (dlsym will give us the address of symbols) and dynamic
       relocation otherwise (executable and DLLs). The relocation should be
       done lazily for GOT entry with *_JUMP_SLOT relocation type (the one
       associated to a PLT entry) but is currently done at load time for an
       unknown reason. */

    sym = &((ElfW(Sym) *) symtab_section->data)[sym_index];
    name = (char *) symtab_section->link->data + sym->st_name;

    if (s1->dynsym) {
	if (ELFW(ST_BIND)(sym->st_info) == STB_LOCAL) {
	    /* Hack alarm.  We don't want to emit dynamic symbols
	       and symbol based relocs for STB_LOCAL symbols, but rather
	       want to resolve them directly.  At this point the symbol
	       values aren't final yet, so we must defer this.  We will later
	       have to create a RELATIVE reloc anyway, so we misuse the
	       relocation slot to smuggle the symbol reference until
	       fill_local_got_entries.  Not that the sym_index is
	       relative to symtab_section, not s1->dynsym!  Nevertheless
	       we use s1->dyn_sym so that if this is the first call
	       that got->reloc is correctly created.  Also note that
	       RELATIVE relocs are not normally created for the .got,
	       so the types serves as a marker for later (and is retained
	       also for the final output, which is okay because then the
	       got is just normal data).  */
	    put_elf_reloc(s1->dynsym, s1->got, got_offset, R_RELATIVE,
			  sym_index);
	} else {
	    if (0 == attr->dyn_index)
                attr->dyn_index = set_elf_sym(s1->dynsym, sym->st_value, size,
					      info, 0, sym->st_shndx, name);
	    put_elf_reloc(s1->dynsym, s1->got, got_offset, dyn_reloc_type,
			  attr->dyn_index);
	}
    } else {
        put_elf_reloc(symtab_section, s1->got, got_offset, dyn_reloc_type,
                      sym_index);
    }

    if (need_plt_entry) {
        if (!s1->plt) {
    	    s1->plt = new_section(s1, ".plt", SHT_PROGBITS,
    			          SHF_ALLOC | SHF_EXECINSTR);
    	    s1->plt->sh_entsize = 4;
        }

        attr->plt_offset = create_plt_entry(s1, got_offset, attr);

        /* create a symbol 'sym@plt' for the PLT jump vector */
        len = strlen(name);
        if (len > sizeof plt_name - 5)
            len = sizeof plt_name - 5;
        memcpy(plt_name, name, len);
        strcpy(plt_name + len, "@plt");
        attr->plt_sym = put_elf_sym(s1->symtab, attr->plt_offset, sym->st_size,
            ELFW(ST_INFO)(STB_GLOBAL, STT_FUNC), 0, s1->plt->sh_num, plt_name);

    } else {
        attr->got_offset = got_offset;
    }

    return attr;
}

/* build GOT and PLT entries */
ST_FUNC void build_got_entries(TCCState *s1)
{
    Section *s;
    ElfW_Rel *rel;
    ElfW(Sym) *sym;
    int i, type, gotplt_entry, reloc_type, sym_index;
    struct sym_attr *attr;

    for(i = 1; i < s1->nb_sections; i++) {
        s = s1->sections[i];
        if (s->sh_type != SHT_RELX)
            continue;
        /* no need to handle got relocations */
        if (s->link != symtab_section)
            continue;
        for_each_elem(s, 0, rel, ElfW_Rel) {
            type = ELFW(R_TYPE)(rel->r_info);
            gotplt_entry = gotplt_entry_type(type);
            sym_index = ELFW(R_SYM)(rel->r_info);
            sym = &((ElfW(Sym) *)symtab_section->data)[sym_index];

            if (gotplt_entry == NO_GOTPLT_ENTRY) {
                continue;
            }

            /* Automatically create PLT/GOT [entry] if it is an undefined
	       reference (resolved at runtime), or the symbol is absolute,
	       probably created by tcc_add_symbol, and thus on 64-bit
	       targets might be too far from application code.  */
            if (gotplt_entry == AUTO_GOTPLT_ENTRY) {
                if (sym->st_shndx == SHN_UNDEF) {
                    ElfW(Sym) *esym;
		    int dynindex;
                    if (s1->output_type == TCC_OUTPUT_DLL && ! PCRELATIVE_DLLPLT)
                        continue;
		    /* Relocations for UNDEF symbols would normally need
		       to be transferred into the executable or shared object.
		       If that were done AUTO_GOTPLT_ENTRY wouldn't exist.
		       But TCC doesn't do that (at least for exes), so we
		       need to resolve all such relocs locally.  And that
		       means PLT slots for functions in DLLs and COPY relocs for
		       data symbols.  COPY relocs were generated in
		       bind_exe_dynsyms (and the symbol adjusted to be defined),
		       and for functions we were generated a dynamic symbol
		       of function type.  */
		    if (s1->dynsym) {
			/* dynsym isn't set for -run :-/  */
			dynindex = get_sym_attr(s1, sym_index, 0)->dyn_index;
			esym = (ElfW(Sym) *)s1->dynsym->data + dynindex;
			if (dynindex
			    && (ELFW(ST_TYPE)(esym->st_info) == STT_FUNC
				|| (ELFW(ST_TYPE)(esym->st_info) == STT_NOTYPE
				    && ELFW(ST_TYPE)(sym->st_info) == STT_FUNC)))
			    goto jmp_slot;
		    }
                } else if (!(sym->st_shndx == SHN_ABS
#ifndef TCC_TARGET_ARM
			&& PTR_SIZE == 8
#endif
			))
                    continue;
            }

#ifdef TCC_TARGET_X86_64
            if ((type == R_X86_64_PLT32 || type == R_X86_64_PC32) &&
                (ELFW(ST_VISIBILITY)(sym->st_other) != STV_DEFAULT ||
		 ELFW(ST_BIND)(sym->st_info) == STB_LOCAL)) {
                rel->r_info = ELFW(R_INFO)(sym_index, R_X86_64_PC32);
                continue;
            }
#endif
            if (code_reloc(type)) {
            jmp_slot:
                reloc_type = R_JMP_SLOT;
            } else
                reloc_type = R_GLOB_DAT;

            if (!s1->got)
                build_got(s1);

            if (gotplt_entry == BUILD_GOT_ONLY)
                continue;

            attr = put_got_entry(s1, reloc_type, sym->st_size, sym->st_info,
                                 sym_index);

            if (reloc_type == R_JMP_SLOT)
                rel->r_info = ELFW(R_INFO)(attr->plt_sym, type);
        }
    }
}

/* put dynamic tag */
static void put_dt(Section *dynamic, int dt, addr_t val)
{
    ElfW(Dyn) *dyn;
    dyn = section_ptr_add(dynamic, sizeof(ElfW(Dyn)));
    dyn->d_tag = dt;
    dyn->d_un.d_val = val;
}

#ifndef TCC_TARGET_PE
static void add_init_array_defines(TCCState *s1, const char *section_name)
{
    Section *s;
    long end_offset;
    char sym_start[1024];
    char sym_end[1024];

    snprintf(sym_start, sizeof(sym_start), "__%s_start", section_name + 1);
    snprintf(sym_end, sizeof(sym_end), "__%s_end", section_name + 1);

    s = find_section(s1, section_name);
    if (!s) {
        end_offset = 0;
        s = data_section;
    } else {
        end_offset = s->data_offset;
    }

    set_elf_sym(symtab_section,
                0, 0,
                ELFW(ST_INFO)(STB_GLOBAL, STT_NOTYPE), 0,
                s->sh_num, sym_start);
    set_elf_sym(symtab_section,
                end_offset, 0,
                ELFW(ST_INFO)(STB_GLOBAL, STT_NOTYPE), 0,
                s->sh_num, sym_end);
}
#endif

static int tcc_add_support(TCCState *s1, const char *filename)
{
    char buf[1024];
    snprintf(buf, sizeof(buf), "%s/%s", s1->tcc_lib_path, filename);
    return tcc_add_file(s1, buf);
}

#ifdef CONFIG_TCC_BCHECK
ST_FUNC void tcc_add_bcheck(TCCState *s1)
{
    addr_t *ptr;
    int sym_index;
    if (0 == s1->do_bounds_check) return;
    /* XXX: add an object file to do that */
    ptr = section_ptr_add(bounds_section, sizeof(*ptr));
    *ptr = 0;
    set_elf_sym(symtab_section, 0, 0,
                ELFW(ST_INFO)(STB_GLOBAL, STT_NOTYPE), 0,
                bounds_section->sh_num, "__bounds_start");
    /* pull bcheck.o from libtcc1.a */
    sym_index = set_elf_sym(symtab_section, 0, 0,
                ELFW(ST_INFO)(STB_GLOBAL, STT_NOTYPE), 0,
                SHN_UNDEF, "__bound_init");
    if (s1->output_type != TCC_OUTPUT_MEMORY) {
        /* add 'call __bound_init()' in .init section */
        Section *init_section = find_section(s1, ".init");
        unsigned char *pinit = section_ptr_add(init_section, 5);
        pinit[0] = 0xe8;
        write32le(pinit + 1, -4);
        put_elf_reloc(symtab_section, init_section,
            init_section->data_offset - 4, R_386_PC32, sym_index);
            /* R_386_PC32 = R_X86_64_PC32 = 2 */
    }
}
#endif

/* add tcc runtime libraries */
ST_FUNC void tcc_add_runtime(TCCState *s1)
{
#ifdef CONFIG_TCC_BCHECK
    tcc_add_bcheck(s1);
#endif
    tcc_add_pragma_libs(s1);
    /* add libc */
// JJX    if( !s1->nostdlib ) {
        tcc_add_library_err(s1, "c");
#ifdef TCC_LIBGCC
        if( !s1->static_link ) {
            if( TCC_LIBGCC[0] == '/' )  tcc_add_file( s1, TCC_LIBGCC );
            else                        tcc_add_dll( s1, TCC_LIBGCC, 0);
        }
#endif
        tcc_add_support(s1, TCC_LIBTCC1);
        /* add crt end if not memory output */
        if( s1->output_type != TCC_OUTPUT_MEMORY )  tcc_add_crt(s1, "crtn.o");
// JJX    }
}

/* add various standard linker symbols (must be done after the
   sections are filled (for example after allocating common
   symbols)) */
static void tcc_add_linker_symbols(TCCState *s1)
{
    char buf[1024];
    int i;
    Section *s;

    set_elf_sym(symtab_section,
                text_section->data_offset, 0,
                ELFW(ST_INFO)(STB_GLOBAL, STT_NOTYPE), 0,
                text_section->sh_num, "_etext");
    set_elf_sym(symtab_section,
                data_section->data_offset, 0,
                ELFW(ST_INFO)(STB_GLOBAL, STT_NOTYPE), 0,
                data_section->sh_num, "_edata");
    set_elf_sym(symtab_section,
                bss_section->data_offset, 0,
                ELFW(ST_INFO)(STB_GLOBAL, STT_NOTYPE), 0,
                bss_section->sh_num, "_end");
#ifndef TCC_TARGET_PE
    /* horrible new standard ldscript defines */
    add_init_array_defines(s1, ".preinit_array");
    add_init_array_defines(s1, ".init_array");
    add_init_array_defines(s1, ".fini_array");
#endif

    /* add start and stop symbols for sections whose name can be
       expressed in C */
    for(i = 1; i < s1->nb_sections; i++) {
        s = s1->sections[i];
        if (s->sh_type == SHT_PROGBITS &&
            (s->sh_flags & SHF_ALLOC)) {
            const char *p;
            int ch;

            /* check if section name can be expressed in C */
            p = s->name;
            for(;;) {
                ch = *p;
                if (!ch)
                    break;
                if (!isid(ch) && !isnum(ch))
                    goto next_sec;
                p++;
            }
            snprintf(buf, sizeof(buf), "__start_%s", s->name);
            set_elf_sym(symtab_section,
                        0, 0,
                        ELFW(ST_INFO)(STB_GLOBAL, STT_NOTYPE), 0,
                        s->sh_num, buf);
            snprintf(buf, sizeof(buf), "__stop_%s", s->name);
            set_elf_sym(symtab_section,
                        s->data_offset, 0,
                        ELFW(ST_INFO)(STB_GLOBAL, STT_NOTYPE), 0,
                        s->sh_num, buf);
        }
    next_sec: ;
    }
}

ST_FUNC void resolve_common_syms(TCCState *s1)
{
    ElfW(Sym) *sym;

    /* Allocate common symbols in BSS.  */
    for_each_elem(symtab_section, 1, sym, ElfW(Sym)) {
        if (sym->st_shndx == SHN_COMMON) {
            /* symbol alignment is in st_value for SHN_COMMONs */
	    sym->st_value = section_add(bss_section, sym->st_size,
					sym->st_value);
            sym->st_shndx = bss_section->sh_num;
        }
    }

    /* Now assign linker provided symbols their value.  */
    tcc_add_linker_symbols(s1);
}

static void tcc_output_binary(TCCState *s1, FILE *f,
                              const int *sec_order)
{
    Section *s;
    int i, offset, size;

    offset = 0;
    for(i=1;i<s1->nb_sections;i++) {
        s = s1->sections[sec_order[i]];
        if (s->sh_type != SHT_NOBITS &&
            (s->sh_flags & SHF_ALLOC)) {
            while (offset < s->sh_offset) {
                fputc(0, f);
                offset++;
            }
            size = s->sh_size;
            fwrite(s->data, 1, size, f);
            offset += size;
        }
    }
}

/* See put_got_entry for a description.  This is the second stage
   where GOT references to local defined symbols are rewritten.  */
static void fill_local_got_entries(TCCState *s1)
{
    ElfW_Rel *rel;
    for_each_elem(s1->got->reloc, 0, rel, ElfW_Rel) {
	if (ELFW(R_TYPE)(rel->r_info) == R_RELATIVE) {
	    int sym_index = ELFW(R_SYM) (rel->r_info);
	    ElfW(Sym) *sym = &((ElfW(Sym) *) symtab_section->data)[sym_index];
	    struct sym_attr *attr = get_sym_attr(s1, sym_index, 0);
	    unsigned offset = attr->got_offset;
	    if (offset != rel->r_offset - s1->got->sh_addr)  tcc_error(1, "huh");
	    rel->r_info = ELFW(R_INFO)(0, R_RELATIVE);
#if SHT_RELX == SHT_RELA
	    rel->r_addend = sym->st_value;
#else
	    /* All our REL architectures also happen to be 32bit LE.  */
	    write32le(s1->got->data + offset, sym->st_value);
#endif
	}
    }
}

/* Bind symbols of executable: resolve undefined symbols from exported symbols
   in shared libraries and export non local defined symbols to shared libraries
   if -rdynamic switch was given on command line */
// static void bind_exe_dynsyms(TCCState *s1) { }

/* Bind symbols of libraries: export all non local symbols of executable that
   are referenced by shared libraries. The reason is that the dynamic loader
   search symbol first in executable and then in libraries. Therefore a
   reference to a symbol already defined by a library can still be resolved by
   a symbol in the executable. */
// static void bind_libs_dynsyms(TCCState *s1) { }

/* Export all non local symbols. This is used by shared libraries so that the
   non local symbols they define can resolve a reference in another shared
   library or in the executable. Correspondingly, it allows undefined local
   symbols to be resolved by other shared libraries or by the executable. */
static void export_global_syms(TCCState *s1)
{
    int dynindex, index;
    const char *name;
    ElfW(Sym) *sym;

    for_each_elem(symtab_section, 1, sym, ElfW(Sym)) {
        if (ELFW(ST_BIND)(sym->st_info) != STB_LOCAL) {
	    name = (char *) symtab_section->link->data + sym->st_name;
	    dynindex = put_elf_sym(s1->dynsym, sym->st_value, sym->st_size,
				   sym->st_info, 0, sym->st_shndx, name);
	    index = sym - (ElfW(Sym) *) symtab_section->data;
            get_sym_attr(s1, index, 1)->dyn_index = dynindex;
        }
    }
}

/* Allocate strings for section names and decide if an unallocated section
   should be output.
   NOTE: the strsec section comes last, so its size is also correct ! */
static int alloc_sec_names(TCCState *s1, int file_type, Section *strsec)
{
    int i;
    Section *s;
    int textrel = 0;

    /* Allocate strings for section names */
    for(i = 1; i < s1->nb_sections; i++) {
        s = s1->sections[i];
        /* when generating a DLL, we include relocations but we may
           patch them */
        if( file_type == TCC_OUTPUT_DLL && s->sh_type == SHT_RELX &&
            !(s->sh_flags & SHF_ALLOC) && (s1->sections[s->sh_info]->sh_flags & SHF_ALLOC) &&
            prepare_dynamic_rel(s1, s)) {
                if( s1->sections[s->sh_info]->sh_flags & SHF_EXECINSTR )  textrel = 1;
        }
        else if(
#if defined CONFIG_TCC_GDEBUG
                 s1->do_debug ||
#endif
                                 file_type == TCC_OUTPUT_OBJ ||
            (s->sh_flags & SHF_ALLOC) || i == (s1->nb_sections - 1)) {
            /* we output all sections if debug or object file */
            s->sh_size = s->data_offset;
        }
	if (s->sh_size || (s->sh_flags & SHF_ALLOC))
            s->sh_name = put_elf_str(strsec, s->name);
    }
    strsec->sh_size = strsec->data_offset;
    return textrel;
}

/* Info to be copied in dynamic section */
struct dyn_inf {
    Section *dynamic;
    Section *dynstr;
    unsigned long data_offset;
    addr_t rel_addr;
    addr_t rel_size;
#if defined(__FreeBSD__) || defined(__FreeBSD_kernel__)
    addr_t bss_addr;
    addr_t bss_size;
#endif
};

/* Assign sections to segments and decide how are sections laid out when loaded
   in memory. This function also fills corresponding program headers. */
static int layout_sections(TCCState *s1, ElfW(Phdr) *phdr, int phnum,
                           Section *interp, Section* strsec,
                           struct dyn_inf *dyninf, int *sec_order)
{
    int i, j, k, file_type, sh_order_index, file_offset;
    unsigned long s_align;
    long long tmp;
    addr_t addr;
    ElfW(Phdr) *ph;
    Section *s;

    file_type = s1->output_type;
    sh_order_index = 1;
    file_offset = 0;
    if (s1->output_format == TCC_OUTPUT_FORMAT_ELF)
        file_offset = sizeof(ElfW(Ehdr)) + phnum * sizeof(ElfW(Phdr));
    s_align = ELF_PAGE_SIZE;
    if (s1->section_align)
        s_align = s1->section_align;

    if (phnum > 0) {
        if (s1->has_text_addr) {
            int a_offset, p_offset;
            addr = s1->text_addr;
            /* we ensure that (addr % ELF_PAGE_SIZE) == file_offset %
               ELF_PAGE_SIZE */
            a_offset = (int) (addr & (s_align - 1));
            p_offset = file_offset & (s_align - 1);
            if (a_offset < p_offset)
                a_offset += s_align;
            file_offset += (a_offset - p_offset);
        } else {
            if (file_type == TCC_OUTPUT_DLL)
                addr = 0;
            else
                addr = ELF_START_ADDR;
            /* compute address after headers */
            addr += (file_offset & (s_align - 1));
        }

        ph = &phdr[0];
        /* Leave one program headers for the program interpreter and one for
           the program header table itself if needed. These are done later as
           they require section layout to be done first. */
        if (interp)
            ph += 2;

        /* dynamic relocation table information, for .dynamic section */
        dyninf->rel_addr = dyninf->rel_size = 0;
#if defined(__FreeBSD__) || defined(__FreeBSD_kernel__)
        dyninf->bss_addr = dyninf->bss_size = 0;
#endif

        for(j = 0; j < 2; j++) {
            ph->p_type = PT_LOAD;
            if (j == 0)
                ph->p_flags = PF_R | PF_X;
            else
                ph->p_flags = PF_R | PF_W;
            ph->p_align = s_align;

            /* Decide the layout of sections loaded in memory. This must
               be done before program headers are filled since they contain
               info about the layout. We do the following ordering: interp,
               symbol tables, relocations, progbits, nobits */
            /* XXX: do faster and simpler sorting */
            for(k = 0; k < 5; k++) {
                for(i = 1; i < s1->nb_sections; i++) {
                    s = s1->sections[i];
                    /* compute if section should be included */
                    if (j == 0) {
                        if ((s->sh_flags & (SHF_ALLOC | SHF_WRITE)) !=
                            SHF_ALLOC)
                            continue;
                    } else {
                        if ((s->sh_flags & (SHF_ALLOC | SHF_WRITE)) !=
                            (SHF_ALLOC | SHF_WRITE))
                            continue;
                    }
                    if (s == interp) {
                        if (k != 0)
                            continue;
                    } else if (s->sh_type == SHT_DYNSYM ||
                               s->sh_type == SHT_STRTAB ||
                               s->sh_type == SHT_HASH) {
                        if (k != 1)
                            continue;
                    } else if (s->sh_type == SHT_RELX) {
                        if (k != 2)
                            continue;
                    } else if (s->sh_type == SHT_NOBITS) {
                        if (k != 4)
                            continue;
                    } else {
                        if (k != 3)
                            continue;
                    }
                    sec_order[sh_order_index++] = i;

                    /* section matches: we align it and add its size */
                    tmp = addr;
                    addr = (addr + s->sh_addralign - 1) &
                        ~(s->sh_addralign - 1);
                    file_offset += (int) ( addr - tmp );
                    s->sh_offset = file_offset;
                    s->sh_addr = addr;

                    /* update program header infos */
                    if (ph->p_offset == 0) {
                        ph->p_offset = file_offset;
                        ph->p_vaddr = addr;
                        ph->p_paddr = ph->p_vaddr;
                    }
                    /* update dynamic relocation infos */
                    if (s->sh_type == SHT_RELX) {
#if defined(__FreeBSD__) || defined(__FreeBSD_kernel__)
                        if (!strcmp(strsec->data + s->sh_name, ".rel.got")) {
                            dyninf->rel_addr = addr;
                            dyninf->rel_size += s->sh_size; /* XXX only first rel. */
                        }
                        if (!strcmp(strsec->data + s->sh_name, ".rel.bss")) {
                            dyninf->bss_addr = addr;
                            dyninf->bss_size = s->sh_size; /* XXX only first rel. */
                        }
#else
                        if (dyninf->rel_size == 0)
                            dyninf->rel_addr = addr;
                        dyninf->rel_size += s->sh_size;
#endif
                    }
                    addr += s->sh_size;
                    if (s->sh_type != SHT_NOBITS)
                        file_offset += s->sh_size;
                }
            }
	    if (j == 0) {
		/* Make the first PT_LOAD segment include the program
		   headers itself (and the ELF header as well), it'll
		   come out with same memory use but will make various
		   tools like binutils strip work better.  */
		ph->p_offset &= ~(ph->p_align - 1);
		ph->p_vaddr &= ~(ph->p_align - 1);
		ph->p_paddr &= ~(ph->p_align - 1);
	    }
            ph->p_filesz = file_offset - ph->p_offset;
            ph->p_memsz = addr - ph->p_vaddr;
            ph++;
            if (j == 0) {
                if (s1->output_format == TCC_OUTPUT_FORMAT_ELF) {
                    /* if in the middle of a page, we duplicate the page in
                       memory so that one copy is RX and the other is RW */
                    if ((addr & (s_align - 1)) != 0)
                        addr += s_align;
                } else {
                    addr = (addr + s_align - 1) & ~(s_align - 1);
                    file_offset = (file_offset + s_align - 1) & ~(s_align - 1);
                }
            }
        }
    }

    /* all other sections come after */
    for(i = 1; i < s1->nb_sections; i++) {
        s = s1->sections[i];
        if (phnum > 0 && (s->sh_flags & SHF_ALLOC))
            continue;
        sec_order[sh_order_index++] = i;

        file_offset = (file_offset + s->sh_addralign - 1) &
            ~(s->sh_addralign - 1);
        s->sh_offset = file_offset;
        if (s->sh_type != SHT_NOBITS)
            file_offset += s->sh_size;
    }

    return file_offset;
}

static void fill_unloadable_phdr(ElfW(Phdr) *phdr, int phnum, Section *interp,
                                 Section *dynamic)
{
    ElfW(Phdr) *ph;

    /* if interpreter, then add corresponding program header */
    if (interp) {
        ph = &phdr[0];

        ph->p_type = PT_PHDR;
        ph->p_offset = sizeof(ElfW(Ehdr));
        ph->p_filesz = ph->p_memsz = phnum * sizeof(ElfW(Phdr));
        ph->p_vaddr = interp->sh_addr - ph->p_filesz;
        ph->p_paddr = ph->p_vaddr;
        ph->p_flags = PF_R | PF_X;
        ph->p_align = 4; /* interp->sh_addralign; */
        ph++;

        ph->p_type = PT_INTERP;
        ph->p_offset = interp->sh_offset;
        ph->p_vaddr = interp->sh_addr;
        ph->p_paddr = ph->p_vaddr;
        ph->p_filesz = interp->sh_size;
        ph->p_memsz = interp->sh_size;
        ph->p_flags = PF_R;
        ph->p_align = interp->sh_addralign;
    }

    /* if dynamic section, then add corresponding program header */
    if (dynamic) {
        ph = &phdr[phnum - 1];

        ph->p_type = PT_DYNAMIC;
        ph->p_offset = dynamic->sh_offset;
        ph->p_vaddr = dynamic->sh_addr;
        ph->p_paddr = ph->p_vaddr;
        ph->p_filesz = dynamic->sh_size;
        ph->p_memsz = dynamic->sh_size;
        ph->p_flags = PF_R | PF_W;
        ph->p_align = dynamic->sh_addralign;
    }
}

/* Fill the dynamic section with tags describing the address and size of
   sections */
static void fill_dynamic(TCCState *s1, struct dyn_inf *dyninf)
{
    Section *dynamic = dyninf->dynamic;

    /* put dynamic section entries */
    put_dt(dynamic, DT_HASH, s1->dynsym->hash->sh_addr);
    put_dt(dynamic, DT_STRTAB, dyninf->dynstr->sh_addr);
    put_dt(dynamic, DT_SYMTAB, s1->dynsym->sh_addr);
    put_dt(dynamic, DT_STRSZ, dyninf->dynstr->data_offset);
    put_dt(dynamic, DT_SYMENT, sizeof(ElfW(Sym)));
#if PTR_SIZE == 8
    put_dt(dynamic, DT_RELA, dyninf->rel_addr);
    put_dt(dynamic, DT_RELASZ, dyninf->rel_size);
    put_dt(dynamic, DT_RELAENT, sizeof(ElfW_Rel));
#else
#if defined(__FreeBSD__) || defined(__FreeBSD_kernel__)
    put_dt(dynamic, DT_PLTGOT, s1->got->sh_addr);
    put_dt(dynamic, DT_PLTRELSZ, dyninf->rel_size);
    put_dt(dynamic, DT_JMPREL, dyninf->rel_addr);
    put_dt(dynamic, DT_PLTREL, DT_REL);
    put_dt(dynamic, DT_REL, dyninf->bss_addr);
    put_dt(dynamic, DT_RELSZ, dyninf->bss_size);
#else
    put_dt(dynamic, DT_REL, dyninf->rel_addr);
    put_dt(dynamic, DT_RELSZ, dyninf->rel_size);
    put_dt(dynamic, DT_RELENT, sizeof(ElfW_Rel));
#endif
#endif
#if defined CONFIG_TCC_GDEBUG
    if( s1->do_debug )  put_dt(dynamic, DT_DEBUG, 0);
#endif
    put_dt(dynamic, DT_NULL, 0);
}

/* Relocate remaining sections and symbols (that is those not related to dynamic linking) */
static int final_sections_reloc(TCCState *s1)
{
    int i;
    Section *s;
    relocate_syms(s1, s1->symtab, 0);
    if( s1->nb_errors )  return -1;
    /* relocate sections */
    /* XXX: ignore sections with allocated relocations ? */
    for(i = 1; i < s1->nb_sections; i++) {
        s = s1->sections[i];
#if defined(TCC_TARGET_I386) || defined(TCC_MUSL)
        if (s->reloc && s != s1->got && (s->sh_flags & SHF_ALLOC)) //gr
        /* On X86 gdb 7.3 works in any case but gdb 6.6 will crash if SHF_ALLOC
        checking is removed */
#else
        if (s->reloc && s != s1->got)
        /* On X86_64 gdb 7.3 will crash if SHF_ALLOC checking is present */
#endif
            relocate_section(s1, s);
    }

    /* relocate relocation entries if the relocation tables are
       allocated in the executable */
    for(i = 1; i < s1->nb_sections; i++) {
        s = s1->sections[i];
        if ((s->sh_flags & SHF_ALLOC) &&
            s->sh_type == SHT_RELX) {
            relocate_rel(s1, s);
        }
    }
    return 0;
}

/* Create an ELF file on disk.
   This function handle ELF specific layout requirements */
static void tcc_output_elf(TCCState *s1, FILE *f, int phnum, ElfW(Phdr) *phdr,
                           int file_offset, int *sec_order)
{
    int i, shnum, offset, size, file_type;
    Section *s;
    ElfW(Ehdr) ehdr;
    ElfW(Shdr) shdr, *sh;

    file_type = s1->output_type;
    shnum = s1->nb_sections;

    memset(&ehdr, 0, sizeof(ehdr));

    if (phnum > 0) {
        ehdr.e_phentsize = sizeof(ElfW(Phdr));
        ehdr.e_phnum = phnum;
        ehdr.e_phoff = sizeof(ElfW(Ehdr));
    }

    /* align to 4 */
    file_offset = (file_offset + 3) & -4;

    /* fill header */
    ehdr.e_ident[0] = ELFMAG0;
    ehdr.e_ident[1] = ELFMAG1;
    ehdr.e_ident[2] = ELFMAG2;
    ehdr.e_ident[3] = ELFMAG3;
    ehdr.e_ident[4] = ELFCLASSW;
    ehdr.e_ident[5] = ELFDATA2LSB;
    ehdr.e_ident[6] = EV_CURRENT;
#if !defined(TCC_TARGET_PE) && (defined(__FreeBSD__) || defined(__FreeBSD_kernel__))
    /* FIXME: should set only for freebsd _target_, but we exclude only PE target */
    ehdr.e_ident[EI_OSABI] = ELFOSABI_FREEBSD;
#endif
#ifdef TCC_TARGET_ARM
#ifdef TCC_ARM_EABI
    ehdr.e_ident[EI_OSABI] = 0;
    ehdr.e_flags = EF_ARM_EABI_VER4;
    if ( file_type == TCC_OUTPUT_DLL)
        ehdr.e_flags |= EF_ARM_HASENTRY;
    if (s1->float_abi == ARM_HARD_FLOAT)
        ehdr.e_flags |= EF_ARM_VFP_FLOAT;
    else
        ehdr.e_flags |= EF_ARM_SOFT_FLOAT;
#else
    ehdr.e_ident[EI_OSABI] = ELFOSABI_ARM;
#endif
#endif
    switch(file_type) {
    default:
    case TCC_OUTPUT_DLL:
        ehdr.e_type = ET_DYN;
        ehdr.e_entry = text_section->sh_addr; /* XXX: is it correct ? */
        break;
    case TCC_OUTPUT_OBJ:
        ehdr.e_type = ET_REL;
        break;
    }
    ehdr.e_machine = EM_TCC_TARGET;
    ehdr.e_version = EV_CURRENT;
    ehdr.e_shoff = file_offset;
    ehdr.e_ehsize = sizeof(ElfW(Ehdr));
    ehdr.e_shentsize = sizeof(ElfW(Shdr));
    ehdr.e_shnum = shnum;
    ehdr.e_shstrndx = shnum - 1;

    fwrite(&ehdr, 1, sizeof(ElfW(Ehdr)), f);
    fwrite(phdr, 1, phnum * sizeof(ElfW(Phdr)), f);
    offset = sizeof(ElfW(Ehdr)) + phnum * sizeof(ElfW(Phdr));

    sort_syms(s1, symtab_section);
    for(i = 1; i < s1->nb_sections; i++) {
        s = s1->sections[sec_order[i]];
        if (s->sh_type != SHT_NOBITS) {
            while (offset < s->sh_offset) {
                fputc(0, f);
                offset++;
            }
            size = s->sh_size;
            if (size)
                fwrite(s->data, 1, size, f);
            offset += size;
        }
    }

    /* output section headers */
    while (offset < ehdr.e_shoff) {
        fputc(0, f);
        offset++;
    }

    for(i = 0; i < s1->nb_sections; i++) {
        sh = &shdr;
        memset(sh, 0, sizeof(ElfW(Shdr)));
        s = s1->sections[i];
        if (s) {
            sh->sh_name = s->sh_name;
            sh->sh_type = s->sh_type;
            sh->sh_flags = s->sh_flags;
            sh->sh_entsize = s->sh_entsize;
            sh->sh_info = s->sh_info;
            if (s->link)
                sh->sh_link = s->link->sh_num;
            sh->sh_addralign = s->sh_addralign;
            sh->sh_addr = s->sh_addr;
            sh->sh_offset = s->sh_offset;
            sh->sh_size = s->sh_size;
        }
        fwrite(sh, 1, sizeof(ElfW(Shdr)), f);
    }
}

/* Write an elf, coff or "binary" file */
static int tcc_write_elf_file(TCCState *s1, const char *filename, int phnum,
                              ElfW(Phdr) *phdr, int file_offset, int *sec_order)
{
    int fd, mode, file_type;
    FILE *f;

    file_type = s1->output_type;
    if (file_type == TCC_OUTPUT_OBJ)
        mode = 0666;
    else
        mode = 0777;
    unlink(filename);
    fd = open(filename, O_WRONLY | O_CREAT | O_TRUNC | O_BINARY, mode);
    if (fd < 0) {
        tcc_error(1, "could not write '%s'", filename);
        return -1;
    }
    f = fdopen(fd, "wb");
    if( s1->verbose )  (void) fprintf( jjglob_dbgfh, " JJVERBOSE:  <- %s\n", filename );

#ifdef TCC_TARGET_COFF
    if (s1->output_format == TCC_OUTPUT_FORMAT_COFF)
        tcc_output_coff(s1, f);
    else
#endif
    if (s1->output_format == TCC_OUTPUT_FORMAT_ELF)
        tcc_output_elf(s1, f, phnum, phdr, file_offset, sec_order);
    else
        tcc_output_binary(s1, f, sec_order);
    fclose(f);

    return 0;
}

/* Sort section headers by assigned sh_addr, remove sections
   that we aren't going to output.  */
static void tidy_section_headers(TCCState *s1, int *sec_order)
{
    int i, nnew, l, *backmap;
    Section **snew, *s;
    ElfW(Sym) *sym;

    snew = tcc_malloc(s1->nb_sections * sizeof(snew[0]));
    backmap = tcc_malloc(s1->nb_sections * sizeof(backmap[0]));
    for (i = 0, nnew = 0, l = s1->nb_sections; i < s1->nb_sections; i++) {
	s = s1->sections[sec_order[i]];
	if (!i || s->sh_name) {
	    backmap[sec_order[i]] = nnew;
	    snew[nnew] = s;
	    ++nnew;
	} else {
	    backmap[sec_order[i]] = 0;
	    snew[--l] = s;
	}
    }
    for (i = 0; i < nnew; i++) {
	s = snew[i];
	if (s) {
	    s->sh_num = i;
            if (s->sh_type == SHT_RELX)
		s->sh_info = backmap[s->sh_info];
	}
    }

    for_each_elem(symtab_section, 1, sym, ElfW(Sym))
	if (sym->st_shndx != SHN_UNDEF && sym->st_shndx < SHN_LORESERVE)
	    sym->st_shndx = backmap[sym->st_shndx];
    if( !s1->static_link ) {
        for_each_elem(s1->dynsym, 1, sym, ElfW(Sym))
	    if (sym->st_shndx != SHN_UNDEF && sym->st_shndx < SHN_LORESERVE)
	        sym->st_shndx = backmap[sym->st_shndx];
    }
    for (i = 0; i < s1->nb_sections; i++)
	sec_order[i] = i;
    tcc_free(s1->sections);
    s1->sections = snew;
    s1->nb_sections = nnew;
    tcc_free(backmap);
}

/* Output an elf, coff or binary file   XXX: suppress unneeded sections */
static int elf_output_file(TCCState *s1, const char *filename)
{
    int i, ret, phnum, shnum, file_type, file_offset, *sec_order;
    struct dyn_inf dyninf = {0};
    ElfW(Phdr) *phdr;
    ElfW(Sym) *sym;
    Section *strsec, *interp, *dynamic, *dynstr;
    int textrel;

    file_type = s1->output_type;
    s1->nb_errors = 0;
    ret = -1;
    phdr = NULL;
    sec_order = NULL;
    interp = dynamic = dynstr = NULL; /* avoid warning */
    textrel = 0;

    if (file_type != TCC_OUTPUT_OBJ) {
        /* if linking, also link in runtime libraries (libc, libgcc, etc.) */
        tcc_add_runtime(s1);
	resolve_common_syms(s1);

        if( !s1->static_link ) {
            /* add dynamic symbol table */
            s1->dynsym = new_symtab(s1, ".dynsym", SHT_DYNSYM, SHF_ALLOC, ".dynstr", ".hash", SHF_ALLOC);
            dynstr = s1->dynsym->link;
            /* add dynamic section */
            dynamic = new_section(s1, ".dynamic", SHT_DYNAMIC, SHF_ALLOC | SHF_WRITE);
            dynamic->link = dynstr;
            dynamic->sh_entsize = sizeof(ElfW(Dyn));
            build_got(s1);
            /* shared library case: simply export all global symbols */
            export_global_syms(s1);
        }
        build_got_entries(s1);
    }

    /* we add a section for symbols */
    strsec = new_section(s1, ".shstrtab", SHT_STRTAB, 0);
    put_elf_str(strsec, "");

    /* Allocate strings for section names */
    textrel = alloc_sec_names(s1, file_type, strsec);

    if (dynamic) {
        /* add a list of needed dlls */
        for(i = 0; i < s1->nb_loaded_dlls; i++) {
            DLLReference *dllref = s1->loaded_dlls[i];
            if (dllref->level == 0)
                put_dt(dynamic, DT_NEEDED, put_elf_str(dynstr, dllref->name));
        }

        if (s1->rpath)
            put_dt(dynamic, s1->enable_new_dtags ? DT_RUNPATH : DT_RPATH,
                   put_elf_str(dynstr, s1->rpath));

        if( TCC_OUTPUT_DLL == file_type ) {
            if( s1->soname )  put_dt(dynamic, DT_SONAME, put_elf_str(dynstr, s1->soname));
            /* XXX: currently, since we do not handle PIC code, we must relocate the readonly segments */
            if( textrel )  put_dt(dynamic, DT_TEXTREL, 0);
        }

        if (s1->symbolic)
            put_dt(dynamic, DT_SYMBOLIC, 0);

        dyninf.dynamic = dynamic;
        dyninf.dynstr = dynstr;
        /* remember offset and reserve space for 2nd call below */
        dyninf.data_offset = dynamic->data_offset;
        fill_dynamic(s1, &dyninf);
        dynamic->sh_size = dynamic->data_offset;
        dynstr->sh_size = dynstr->data_offset;
    }

    /* compute number of program headers */
    if( file_type == TCC_OUTPUT_OBJ )       phnum = 0;
    else if( file_type == TCC_OUTPUT_DLL )  phnum = 3;
    else if( s1->static_link )              phnum = 2;
    else                                    phnum = 5;

    /* allocate program segment headers */
    phdr = tcc_mallocz(phnum * sizeof(ElfW(Phdr)));

    /* compute number of sections */
    shnum = s1->nb_sections;

    /* this array is used to reorder sections in the output file */
    sec_order = tcc_malloc(sizeof(int) * shnum);
    sec_order[0] = 0;

    /* compute section to program header mapping */
    file_offset = layout_sections(s1, phdr, phnum, interp, strsec, &dyninf,
                                  sec_order);

    /* Fill remaining program header and finalize relocation related to dynamic
       linking. */
    if (file_type != TCC_OUTPUT_OBJ) {
        fill_unloadable_phdr(phdr, phnum, interp, dynamic);
        if (dynamic) {
            dynamic->data_offset = dyninf.data_offset;
            fill_dynamic(s1, &dyninf);

            /* put in GOT the dynamic section address and relocate PLT */
            write32le(s1->got->data, dynamic->sh_addr);
            if ( RELOCATE_DLLPLT && file_type == TCC_OUTPUT_DLL ) relocate_plt(s1);

            /* relocate symbols in .dynsym now that final addresses are known */
            for_each_elem(s1->dynsym, 1, sym, ElfW(Sym)) {
                if (sym->st_shndx != SHN_UNDEF && sym->st_shndx < SHN_LORESERVE) {
                    /* do symbol relocation */
                    sym->st_value += s1->sections[sym->st_shndx]->sh_addr;
                }
            }
        }

        /* if building executable or DLL, then relocate each section
           except the GOT which is already relocated */
        ret = final_sections_reloc(s1);
        if (ret)
            goto the_end;
	tidy_section_headers(s1, sec_order);

        /* Perform relocation to GOT or PLT entries */
        if (s1->got) fill_local_got_entries(s1);
    }

    /* Create the ELF file with name 'filename' */
    ret = tcc_write_elf_file(s1, filename, phnum, phdr, file_offset, sec_order);
    s1->nb_sections = shnum;
 the_end:
    tcc_free(sec_order);
    tcc_free(phdr);
    return ret;
}

LIBTCCAPI int tcc_output_file(TCCState *s, const char *filename)
{
    int ret;
#ifdef TCC_TARGET_PE
    if (s->output_type != TCC_OUTPUT_OBJ) {
        ret = pe_output_file(s, filename);
    } else
#endif
        ret = elf_output_file(s, filename);
    return ret;
}

static void *load_data(int fd, unsigned long file_offset, unsigned long size)
{
    void *data;

    data = tcc_malloc(size);
    lseek(fd, file_offset, SEEK_SET);
    read(fd, data, size);
    return data;
}

typedef struct SectionMergeInfo {
    Section *s;            /* corresponding existing section */
    unsigned long offset;  /* offset of the new section in the existing section */
    uint8_t new_section;       /* true if section 's' was added */
    uint8_t link_once;         /* true if link once section */
} SectionMergeInfo;

ST_FUNC int tcc_object_type(int fd, ElfW(Ehdr) *h)
{
    int size = read(fd, h, sizeof *h);
    if (size == sizeof *h && 0 == memcmp(h, ELFMAG, 4)) {
        if (h->e_type == ET_REL)
            return AFF_BINTYPE_REL;
        if (h->e_type == ET_DYN)
            return AFF_BINTYPE_DYN;
    } else if (size >= 8) {
        if (0 == memcmp(h, ARMAG, 8))
            return AFF_BINTYPE_AR;
#ifdef TCC_TARGET_COFF
        if (((struct filehdr*)h)->f_magic == COFF_C67_MAGIC)
            return AFF_BINTYPE_C67;
#endif
    }
    return 0;
}

/* load an object file and merge it with current files */
/* XXX: handle correctly stab (debug) info */
ST_FUNC int tcc_load_object_file(TCCState *s1,
                                int fd, unsigned long file_offset)
{
    ElfW(Ehdr) ehdr;
    ElfW(Shdr) *shdr, *sh;
    int size, i, j, offset, offseti, nb_syms, sym_index, ret, seencompressed;
    unsigned char *strsec, *strtab;
    int *old_to_new_syms;
    char *sh_name, *name;
    SectionMergeInfo *sm_table, *sm;
    ElfW(Sym) *sym, *symtab;
    ElfW_Rel *rel;
    Section *s;

    int stab_index;
    int stabstr_index;

    stab_index = stabstr_index = 0;

    lseek(fd, file_offset, SEEK_SET);
    if (tcc_object_type(fd, &ehdr) != AFF_BINTYPE_REL)
        goto fail1;
    /* test CPU specific stuff */
    if (ehdr.e_ident[5] != ELFDATA2LSB ||
        ehdr.e_machine != EM_TCC_TARGET) {
    fail1:
        tcc_error(1, "invalid object file");
        return -1;
    }
    /* read sections */
    shdr = load_data(fd, file_offset + ehdr.e_shoff,
                     sizeof(ElfW(Shdr)) * ehdr.e_shnum);
    sm_table = tcc_mallocz(sizeof(SectionMergeInfo) * ehdr.e_shnum);

    /* load section names */
    sh = &shdr[ehdr.e_shstrndx];
    strsec = load_data(fd, file_offset + sh->sh_offset, sh->sh_size);

    /* load symtab and strtab */
    old_to_new_syms = NULL;
    symtab = NULL;
    strtab = NULL;
    nb_syms = 0;
    seencompressed = 0;
    for(i = 1; i < ehdr.e_shnum; i++) {
        sh = &shdr[i];
        if (sh->sh_type == SHT_SYMTAB) {
            if (symtab) {
                tcc_error(1, "object must contain only one symtab");
            fail:
                ret = -1;
                goto the_end;
            }
            nb_syms = sh->sh_size / sizeof(ElfW(Sym));
            symtab = load_data(fd, file_offset + sh->sh_offset, sh->sh_size);
            sm_table[i].s = symtab_section;

            /* now load strtab */
            sh = &shdr[sh->sh_link];
            strtab = load_data(fd, file_offset + sh->sh_offset, sh->sh_size);
        }
	if (sh->sh_flags & SHF_COMPRESSED)
	    seencompressed = 1;
    }

    /* now examine each section and try to merge its content with the
       ones in memory */
    for(i = 1; i < ehdr.e_shnum; i++) {
        /* no need to examine section name strtab */
        if (i == ehdr.e_shstrndx)
            continue;
        sh = &shdr[i];
        sh_name = (char *) strsec + sh->sh_name;
        /* ignore sections types we do not handle */
        if (sh->sh_type != SHT_PROGBITS &&
            sh->sh_type != SHT_RELX &&
#ifdef TCC_ARM_EABI
            sh->sh_type != SHT_ARM_EXIDX &&
#endif
            sh->sh_type != SHT_NOBITS &&
            sh->sh_type != SHT_PREINIT_ARRAY &&
            sh->sh_type != SHT_INIT_ARRAY &&
            sh->sh_type != SHT_FINI_ARRAY &&
            strcmp(sh_name, ".stabstr")
            )
            continue;
	if (seencompressed
	    && (!strncmp(sh_name, ".debug_", sizeof(".debug_")-1)
		|| (sh->sh_type == SHT_RELX
		    && !strncmp((char*)strsec + shdr[sh->sh_info].sh_name,
			        ".debug_", sizeof(".debug_")-1))))
	  continue;
        if (sh->sh_addralign < 1)
            sh->sh_addralign = 1;
        /* find corresponding section, if any */
        for(j = 1; j < s1->nb_sections;j++) {
            s = s1->sections[j];
            if (!strcmp(s->name, sh_name)) {
                if (!strncmp(sh_name, ".gnu.linkonce",
                             sizeof(".gnu.linkonce") - 1)) {
                    /* if a 'linkonce' section is already present, we
                       do not add it again. It is a little tricky as
                       symbols can still be defined in
                       it. */
                    sm_table[i].link_once = 1;
                    goto next;
                } else {
                    goto found;
                }
            }
        }
        /* not found: create new section */
        s = new_section(s1, sh_name, sh->sh_type, sh->sh_flags & ~SHF_GROUP);
        /* take as much info as possible from the section. sh_link and
           sh_info will be updated later */
        s->sh_addralign = sh->sh_addralign;
        s->sh_entsize = sh->sh_entsize;
        sm_table[i].new_section = 1;
    found:
        if (sh->sh_type != s->sh_type) {
            tcc_error(1, "invalid section type");
            goto fail;
        }

        /* align start of section */
        offset = s->data_offset;

        if (0 == strcmp(sh_name, ".stab")) {
            stab_index = i;
            goto no_align;
        }
        if (0 == strcmp(sh_name, ".stabstr")) {
            stabstr_index = i;
            goto no_align;
        }

        size = sh->sh_addralign - 1;
        offset = (offset + size) & ~size;
        if (sh->sh_addralign > s->sh_addralign)
            s->sh_addralign = sh->sh_addralign;
        s->data_offset = offset;
    no_align:
        sm_table[i].offset = offset;
        sm_table[i].s = s;
        /* concatenate sections */
        size = sh->sh_size;
        if (sh->sh_type != SHT_NOBITS) {
            unsigned char *ptr;
            lseek(fd, file_offset + sh->sh_offset, SEEK_SET);
            ptr = section_ptr_add(s, size);
            read(fd, ptr, size);
        } else {
            s->data_offset += size;
        }
    next: ;
    }

    /* gr relocate stab strings */
    if (stab_index && stabstr_index) {
        Stab_Sym *a, *b;
        unsigned o;
        s = sm_table[stab_index].s;
        a = (Stab_Sym *)(s->data + sm_table[stab_index].offset);
        b = (Stab_Sym *)(s->data + s->data_offset);
        o = sm_table[stabstr_index].offset;
        while (a < b)
            a->n_strx += o, a++;
    }

    /* second short pass to update sh_link and sh_info fields of new
       sections */
    for(i = 1; i < ehdr.e_shnum; i++) {
        s = sm_table[i].s;
        if (!s || !sm_table[i].new_section)
            continue;
        sh = &shdr[i];
        if (sh->sh_link > 0)
            s->link = sm_table[sh->sh_link].s;
        if (sh->sh_type == SHT_RELX) {
            s->sh_info = sm_table[sh->sh_info].s->sh_num;
            /* update backward link */
            s1->sections[s->sh_info]->reloc = s;
        }
    }
    sm = sm_table;

    /* resolve symbols */
    old_to_new_syms = tcc_mallocz(nb_syms * sizeof(int));

    sym = symtab + 1;
    for(i = 1; i < nb_syms; i++, sym++) {
        if (sym->st_shndx != SHN_UNDEF &&
            sym->st_shndx < SHN_LORESERVE) {
            sm = &sm_table[sym->st_shndx];
            if (sm->link_once) {
                /* if a symbol is in a link once section, we use the
                   already defined symbol. It is very important to get
                   correct relocations */
                if (ELFW(ST_BIND)(sym->st_info) != STB_LOCAL) {
                    name = (char *) strtab + sym->st_name;
                    sym_index = find_elf_sym(symtab_section, name);
                    if (sym_index)
                        old_to_new_syms[i] = sym_index;
                }
                continue;
            }
            /* if no corresponding section added, no need to add symbol */
            if (!sm->s)
                continue;
            /* convert section number */
            sym->st_shndx = sm->s->sh_num;
            /* offset value */
            sym->st_value += sm->offset;
        }
        /* add symbol */
        name = (char *) strtab + sym->st_name;
        sym_index = set_elf_sym(symtab_section, sym->st_value, sym->st_size,
                                sym->st_info, sym->st_other,
                                sym->st_shndx, name);
        old_to_new_syms[i] = sym_index;
    }

    /* third pass to patch relocation entries */
    for(i = 1; i < ehdr.e_shnum; i++) {
        s = sm_table[i].s;
        if (!s)
            continue;
        sh = &shdr[i];
        offset = sm_table[i].offset;
        switch(s->sh_type) {
        case SHT_RELX:
            /* take relocation offset information */
            offseti = sm_table[sh->sh_info].offset;
            for_each_elem(s, (offset / sizeof(*rel)), rel, ElfW_Rel) {
                int type;
                unsigned sym_index;
                /* convert symbol index */
                type = ELFW(R_TYPE)(rel->r_info);
                sym_index = ELFW(R_SYM)(rel->r_info);
                /* NOTE: only one symtab assumed */
                if (sym_index >= nb_syms)
                    goto invalid_reloc;
                sym_index = old_to_new_syms[sym_index];
                /* ignore link_once in rel section. */
                if (!sym_index && !sm->link_once
#ifdef TCC_TARGET_ARM
                    && type != R_ARM_V4BX
#endif
                   ) {
                invalid_reloc:
                    tcc_error(1, "Invalid relocation entry [%2d] '%s' @ %.8x",
                        i, strsec + sh->sh_name, rel->r_offset);
                    goto fail;
                }
                rel->r_info = ELFW(R_INFO)(sym_index, type);
                /* offset the relocation offset */
                rel->r_offset += offseti;
#ifdef TCC_TARGET_ARM
                /* Jumps and branches from a Thumb code to a PLT entry need
                   special handling since PLT entries are ARM code.
                   Unconditional bl instructions referencing PLT entries are
                   handled by converting these instructions into blx
                   instructions. Other case of instructions referencing a PLT
                   entry require to add a Thumb stub before the PLT entry to
                   switch to ARM mode. We set bit plt_thumb_stub of the
                   attribute of a symbol to indicate such a case. */
                if (type == R_ARM_THM_JUMP24)
                    get_sym_attr(s1, sym_index, 1)->plt_thumb_stub = 1;
#endif
            }
            break;
        default:
            break;
        }
    }

    ret = 0;
 the_end:
    tcc_free(symtab);
    tcc_free(strtab);
    tcc_free(old_to_new_syms);
    tcc_free(sm_table);
    tcc_free(strsec);
    tcc_free(shdr);
    return ret;
}

typedef struct ArchiveHeader {
    char ar_name[16];           /* name of this member */
    char ar_date[12];           /* file mtime */
    char ar_uid[6];             /* owner uid; printed as decimal */
    char ar_gid[6];             /* owner gid; printed as decimal */
    char ar_mode[8];            /* file mode, printed as octal   */
    char ar_size[10];           /* file size, printed as decimal */
    char ar_fmag[2];            /* should contain ARFMAG */
} ArchiveHeader;

static int get_be32(const uint8_t *b)
{
    return b[3] | (b[2] << 8) | (b[1] << 16) | (b[0] << 24);
}

static long get_be64(const uint8_t *b)
{
  long long ret = get_be32(b);
  ret = (ret << 32) | (unsigned)get_be32(b+4);
  return (long)ret;
}

/* load only the objects which resolve undefined symbols */
static int tcc_load_alacarte(TCCState *s1, int fd, int size, int entrysize)
{
    long i, bound, nsyms, sym_index, off, ret;
    uint8_t *data;
    const char *ar_names, *p;
    const uint8_t *ar_index;
    ElfW(Sym) *sym;

    data = tcc_malloc(size);
    if (read(fd, data, size) != size)
        goto fail;
    nsyms = entrysize == 4 ? get_be32(data) : get_be64(data);
    ar_index = data + entrysize;
    ar_names = (char *) ar_index + nsyms * entrysize;

    do {
        bound = 0;
        for(p = ar_names, i = 0; i < nsyms; i++, p += strlen(p)+1) {
            sym_index = find_elf_sym(symtab_section, p);
            if(sym_index) {
                sym = &((ElfW(Sym) *)symtab_section->data)[sym_index];
                if(sym->st_shndx == SHN_UNDEF) {
                    off = (entrysize == 4
			   ? get_be32(ar_index + i * 4)
			   : get_be64(ar_index + i * 8))
			  + sizeof(ArchiveHeader);
                    ++bound;
                    if(tcc_load_object_file(s1, fd, off) < 0) {
                    fail:
                        ret = -1;
                        goto the_end;
                    }
                }
            }
        }
    } while(bound);
    ret = 0;
 the_end:
    tcc_free(data);
    return ret;
}

/* load a '.a' file */
ST_FUNC int tcc_load_archive(TCCState *s1, int fd)
{
    ArchiveHeader hdr;
    char ar_size[11];
    char ar_name[17];
    char magic[8];
    int size, len, i;
    unsigned long file_offset;

    /* skip magic which was already checked */
    read(fd, magic, sizeof(magic));

    for(;;) {
        len = read(fd, &hdr, sizeof(hdr));
        if (len == 0)
            break;
        if (len != sizeof(hdr)) {
            tcc_error(1, "invalid archive");
            return -1;
        }
        memcpy(ar_size, hdr.ar_size, sizeof(hdr.ar_size));
        ar_size[sizeof(hdr.ar_size)] = '\0';
        size = strtol(ar_size, NULL, 0);
        memcpy(ar_name, hdr.ar_name, sizeof(hdr.ar_name));
        for(i = sizeof(hdr.ar_name) - 1; i >= 0; i--) {
            if (ar_name[i] != ' ')
                break;
        }
        ar_name[i + 1] = '\0';
        file_offset = lseek(fd, 0, SEEK_CUR);
        /* align to even */
        size = (size + 1) & ~1;
        if (!strcmp(ar_name, "/")) {
            /* coff symbol table : we handle it */
            if( !s1->no_alacarte_link ) return tcc_load_alacarte(s1, fd, size, 4);
	} else if (!strcmp(ar_name, "/SYM64/")) {
            if( !s1->no_alacarte_link ) return tcc_load_alacarte(s1, fd, size, 8);
        } else {
            ElfW(Ehdr) ehdr;
            if (tcc_object_type(fd, &ehdr) == AFF_BINTYPE_REL) {
                if (tcc_load_object_file(s1, fd, file_offset) < 0)
                    return -1;
            }
        }
        lseek(fd, file_offset + size, SEEK_SET);
    }
    return 0;
}

#ifndef TCC_TARGET_PE
/* load a DLL and all referenced DLLs. 'level = 0' means that the DLL
   is referenced by the user (so it should be added as DT_NEEDED in
   the generated ELF file) */
ST_FUNC int tcc_load_dll(TCCState *s1, int fd, const char *filename, int level)
{
    ElfW(Ehdr) ehdr;
    ElfW(Shdr) *shdr, *sh, *sh1;
    int i, j, nb_syms, nb_dts, sym_bind, ret;
    ElfW(Sym) *sym, *dynsym;
    ElfW(Dyn) *dt, *dynamic;
    unsigned char *dynstr;
    const char *name, *soname;
    DLLReference *dllref;

    read(fd, &ehdr, sizeof(ehdr));

    /* test CPU specific stuff */
    if (ehdr.e_ident[5] != ELFDATA2LSB ||
        ehdr.e_machine != EM_TCC_TARGET) {
        tcc_error(1, "bad architecture");
        return -1;
    }

    /* read sections */
    shdr = load_data(fd, ehdr.e_shoff, sizeof(ElfW(Shdr)) * ehdr.e_shnum);

    /* load dynamic section and dynamic symbols */
    nb_syms = 0;
    nb_dts = 0;
    dynamic = NULL;
    dynsym = NULL; /* avoid warning */
    dynstr = NULL; /* avoid warning */
    for(i = 0, sh = shdr; i < ehdr.e_shnum; i++, sh++) {
        switch(sh->sh_type) {
        case SHT_DYNAMIC:
            nb_dts = sh->sh_size / sizeof(ElfW(Dyn));
            dynamic = load_data(fd, sh->sh_offset, sh->sh_size);
            break;
        case SHT_DYNSYM:
            nb_syms = sh->sh_size / sizeof(ElfW(Sym));
            dynsym = load_data(fd, sh->sh_offset, sh->sh_size);
            sh1 = &shdr[sh->sh_link];
            dynstr = load_data(fd, sh1->sh_offset, sh1->sh_size);
            break;
        default:
            break;
        }
    }

    /* compute the real library name */
    soname = tcc_basename(filename);

    for(i = 0, dt = dynamic; i < nb_dts; i++, dt++) {
        if (dt->d_tag == DT_SONAME)  soname = (char *) dynstr + dt->d_un.d_val;
    }

    /* if the dll is already loaded, do not load it */
    for(i = 0; i < s1->nb_loaded_dlls; i++) {
        dllref = s1->loaded_dlls[i];
        if (!strcmp(soname, dllref->name)) {
            /* but update level if needed */
            if (level < dllref->level)
                dllref->level = level;
            ret = 0;
            goto the_end;
        }
    }

    /* add the dll and its level */
    dllref = tcc_mallocz(sizeof(DLLReference) + strlen(soname));
    dllref->level = level;
    strcpy(dllref->name, soname);
    dynarray_add(&s1->loaded_dlls, &s1->nb_loaded_dlls, dllref);

    /* add dynamic symbols in dynsym_section */
    for(i = 1, sym = dynsym + 1; i < nb_syms; i++, sym++) {
        sym_bind = ELFW(ST_BIND)(sym->st_info);
        if (sym_bind == STB_LOCAL)
            continue;
        name = (char *) dynstr + sym->st_name;
        set_elf_sym(s1->dynsymtab_section, sym->st_value, sym->st_size,
                    sym->st_info, sym->st_other, sym->st_shndx, name);
    }

    /* load all referenced DLLs */
    for(i = 0, dt = dynamic; i < nb_dts; i++, dt++) {
        switch(dt->d_tag) {
        case DT_NEEDED:
            name = (char *) dynstr + dt->d_un.d_val;
            for(j = 0; j < s1->nb_loaded_dlls; j++) {
                dllref = s1->loaded_dlls[j];
                if (!strcmp(name, dllref->name))
                    goto already_loaded;
            }
            if (tcc_add_dll(s1, name, AFF_REFERENCED_DLL) < 0) {
                tcc_error(1, "referenced dll '%s' not found", name);
                ret = -1;
                goto the_end;
            }
        already_loaded:
            break;
        }
    }
    ret = 0;
 the_end:
    tcc_free(dynstr);
    tcc_free(dynsym);
    tcc_free(dynamic);
    tcc_free(shdr);
    return ret;
}

#define LD_TOK_NAME 256
#define LD_TOK_EOF  (-1)

/* return next ld script token */
static int ld_next(TCCState *s1, char *name, int name_size)
{
    int c;
    char *q;

 redo:
    switch(ch) {
    case ' ':
    case '\t':
    case '\f':
    case '\v':
    case '\r':
    case '\n':
        inp();
        goto redo;
    case '/':
        minp();
        if (ch == '*') {
            file->buf_ptr = parse_comment(file->buf_ptr);
            ch = file->buf_ptr[0];
            goto redo;
        } else {
            q = name;
            *q++ = '/';
            goto parse_name;
        }
        break;
    case '\\':
        ch = handle_eob();
        if (ch != '\\')
            goto redo;
        /* fall through */
    /* case 'a' ... 'z': */
    case 'a':
       case 'b':
       case 'c':
       case 'd':
       case 'e':
       case 'f':
       case 'g':
       case 'h':
       case 'i':
       case 'j':
       case 'k':
       case 'l':
       case 'm':
       case 'n':
       case 'o':
       case 'p':
       case 'q':
       case 'r':
       case 's':
       case 't':
       case 'u':
       case 'v':
       case 'w':
       case 'x':
       case 'y':
       case 'z':
    /* case 'A' ... 'z': */
    case 'A':
       case 'B':
       case 'C':
       case 'D':
       case 'E':
       case 'F':
       case 'G':
       case 'H':
       case 'I':
       case 'J':
       case 'K':
       case 'L':
       case 'M':
       case 'N':
       case 'O':
       case 'P':
       case 'Q':
       case 'R':
       case 'S':
       case 'T':
       case 'U':
       case 'V':
       case 'W':
       case 'X':
       case 'Y':
       case 'Z':
    case '_':
    case '.':
    case '$':
    case '~':
        q = name;
    parse_name:
        for(;;) {
            if (!((ch >= 'a' && ch <= 'z') ||
                  (ch >= 'A' && ch <= 'Z') ||
                  (ch >= '0' && ch <= '9') ||
                  strchr("/.-_+=$:\\,~", ch)))
                break;
            if ((q - name) < name_size - 1) {
                *q++ = ch;
            }
            minp();
        }
        *q = '\0';
        c = LD_TOK_NAME;
        break;
    case CH_EOF:
        c = LD_TOK_EOF;
        break;
    default:
        c = ch;
        inp();
        break;
    }
    return c;
}

static int ld_add_file(TCCState *s1, const char filename[])
{
    if (filename[0] == '/') {
        if (CONFIG_SYSROOT[0] == '\0'
            && tcc_add_file_internal(s1, filename, AFF_TYPE_BIN) == 0)
            return 0;
        filename = tcc_basename(filename);
    }
    return tcc_add_dll(s1, filename, 0);
}

static inline int new_undef_syms(void)
{
    int ret = 0;
    ret = new_undef_sym;
    new_undef_sym = 0;
    return ret;
}

static int ld_add_file_list(TCCState *s1, const char *cmd, int as_needed)
{
    char filename[1024], libname[1024];
    int t, group, nblibs = 0, ret = 0;
    char **libs = NULL;

    group = !strcmp(cmd, "GROUP");
    if (!as_needed)
        new_undef_syms();
    t = ld_next(s1, filename, sizeof(filename));
    if( t != '(' )  tcc_error(-1, "( expected" );
    t = ld_next(s1, filename, sizeof(filename));
    for(;;) {
        libname[0] = '\0';
        if (t == LD_TOK_EOF) {
            tcc_error(1, "unexpected end of file");
            ret = -1;
            goto lib_parse_error;
        } else if (t == ')') {
            break;
        } else if (t == '-') {
            t = ld_next(s1, filename, sizeof(filename));
            if ((t != LD_TOK_NAME) || (filename[0] != 'l')) {
                tcc_error(1, "library name expected");
                ret = -1;
                goto lib_parse_error;
            }
            pstrcpy(libname, sizeof libname, &filename[1]);
            if( s1->static_link )  snprintf(filename, sizeof filename, "lib%s.a",  libname);
            else                   snprintf(filename, sizeof filename, "lib%s.so", libname);
        } else if (t != LD_TOK_NAME) {
            tcc_error(1, "filename expected");
            ret = -1;
            goto lib_parse_error;
        }
        if (!strcmp(filename, "AS_NEEDED")) {
            ret = ld_add_file_list(s1, cmd, 1);
            if (ret)
                goto lib_parse_error;
        } else {
            /* TODO: Implement AS_NEEDED support. Ignore it for now */
            if (!as_needed) {
                ret = ld_add_file(s1, filename);
                if (ret)
                    goto lib_parse_error;
                if (group) {
                    /* Add the filename *and* the libname to avoid future conversions */
                    dynarray_add(&libs, &nblibs, tcc_strdup(filename));
                    if (libname[0] != '\0')
                        dynarray_add(&libs, &nblibs, tcc_strdup(libname));
                }
            }
        }
        t = ld_next(s1, filename, sizeof(filename));
        if (t == ',') {
            t = ld_next(s1, filename, sizeof(filename));
        }
    }
    if (group && !as_needed) {
        while (new_undef_syms()) {
            int i;

            for (i = 0; i < nblibs; i ++)
                ld_add_file(s1, libs[i]);
        }
    }
lib_parse_error:
    dynarray_reset(&libs, &nblibs);
    return ret;
}

/* interpret a subset of GNU ldscripts to handle the dummy libc.so
   files */
ST_FUNC int tcc_load_ldscript(TCCState *s1)
{
    char cmd[64];
    char filename[1024];
    int t, ret;

    ch = handle_eob();
    for(;;) {
        t = ld_next(s1, cmd, sizeof(cmd));
        if (t == LD_TOK_EOF)
            return 0;
        else if (t != LD_TOK_NAME)
            return -1;
        if (!strcmp(cmd, "INPUT") ||
            !strcmp(cmd, "GROUP")) {
            ret = ld_add_file_list(s1, cmd, 0);
            if (ret)
                return ret;
        } else if (!strcmp(cmd, "OUTPUT_FORMAT") ||
                   !strcmp(cmd, "TARGET")) {
            /* ignore some commands */
            t = ld_next(s1, cmd, sizeof(cmd));
            if( t != '(' )  tcc_error(-1, "( expected" );
            for(;;) {
                t = ld_next(s1, filename, sizeof(filename));
                if (t == LD_TOK_EOF) {
                    tcc_error(1, "unexpected end of file");
                    return -1;
                } else if (t == ')') {
                    break;
                }
            }
        } else {
            return -1;
        }
    }
    return 0;
}
#endif /* !TCC_TARGET_PE */

/*  TCC - Tiny C Compiler - Support for -run switch
 *  Copyright (c) 2001-2004 Fabrice Bellard
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */

/* only native compiler supports -run */
#ifdef TCC_IS_NATIVE

#ifndef _WIN32
# include <sys/mman.h>
#endif

#ifdef CONFIG_TCC_BACKTRACE
# ifndef _WIN32
#  include <signal.h>
#  ifndef __OpenBSD__
#   include <sys/ucontext.h>
#  endif
# else
#  define ucontext_t CONTEXT
# endif
ST_DATA int rt_num_callers = 6;
ST_DATA const char **rt_bound_error_msg;
ST_DATA void *rt_prog_main;
static int rt_get_caller_pc(addr_t *paddr, ucontext_t *uc, int level);
static void rt_error(ucontext_t *uc, const char *fmt, ...);
static void set_exception_handler(void);
#endif

static void set_pages_executable(void *ptr, unsigned long length);
static int tcc_relocate_ex(TCCState *s1, void *ptr, addr_t ptr_diff);

#ifdef _WIN64
static void *win64_add_function_table(TCCState *s1);
static void win64_del_function_table(void *);
#endif

/* ------------------------------------------------------------- */
/* Do all relocations (needed before using tcc_get_symbol())
   Returns -1 on error. */

LIBTCCAPI int tcc_relocate(TCCState *s1, void *ptr)
{
    int size;
    addr_t ptr_diff = 0;

    if (TCC_RELOCATE_AUTO != ptr)
        return tcc_relocate_ex(s1, ptr, 0);

    size = tcc_relocate_ex(s1, NULL, 0);
    if (size < 0)
        return -1;

#ifdef HAVE_SELINUX
{
    /* Using mmap instead of malloc */
    void *prx;
    char tmpfname[] = "/tmp/.tccrunXXXXXX";
    int fd = mkstemp(tmpfname);
    unlink(tmpfname);
    ftruncate(fd, size);

    ptr = mmap (NULL, size, PROT_READ|PROT_WRITE, MAP_SHARED, fd, 0);
    prx = mmap (NULL, size, PROT_READ|PROT_EXEC, MAP_SHARED, fd, 0);
    if( ptr == MAP_FAILED || prx == MAP_FAILED )  tcc_error(-1, "tccrun: could not map memory");
    dynarray_add(&s1->runtime_mem, &s1->nb_runtime_mem, (void*)(addr_t)size);
    dynarray_add(&s1->runtime_mem, &s1->nb_runtime_mem, prx);
    ptr_diff = (char*)prx - (char*)ptr;
}
#else
    ptr = tcc_malloc(size);
#endif
    tcc_relocate_ex(s1, ptr, ptr_diff); /* no more errors expected */
    dynarray_add(&s1->runtime_mem, &s1->nb_runtime_mem, ptr);
    return 0;
}

ST_FUNC void tcc_run_free(TCCState *s1)
{
    int i;

    for (i = 0; i < s1->nb_runtime_mem; ++i) {
#ifdef HAVE_SELINUX
        unsigned size = (unsigned)(addr_t)s1->runtime_mem[i++];
        munmap(s1->runtime_mem[i++], size);
        munmap(s1->runtime_mem[i], size);
#else
#ifdef _WIN64
        win64_del_function_table(*(void**)s1->runtime_mem[i]);
#endif
        tcc_free(s1->runtime_mem[i]);
#endif
    }
    tcc_free(s1->runtime_mem);
}

/* launch the compiled program with the given arguments */
LIBTCCAPI int tcc_run(TCCState *s1, int argc, char **argv)
{
    int (*prog_main)(int, char **);

    s1->runtime_main = "main";
    if (tcc_relocate(s1, TCC_RELOCATE_AUTO) < 0)
        return -1;
    prog_main = tcc_get_symbol_err(s1, s1->runtime_main);

#if defined CONFIG_TCC_BACKTRACE && defined CONFIG_TCC_GDEBUG
    if( s1->do_debug ) {
        set_exception_handler();
        rt_prog_main = prog_main;
    }
#endif

    errno = 0; /* clean errno value */

#ifdef CONFIG_TCC_BCHECK
    if (s1->do_bounds_check) {
        void (*bound_init)(void);
        void (*bound_exit)(void);
        void (*bound_new_region)(void *p, addr_t size);
        int  (*bound_delete_region)(void *p);
        int i, ret;

        /* set error function */
        rt_bound_error_msg = tcc_get_symbol_err(s1, "__bound_error_msg");
        /* XXX: use .init section so that it also work in binary ? */
        bound_init = tcc_get_symbol_err(s1, "__bound_init");
        bound_exit = tcc_get_symbol_err(s1, "__bound_exit");
        bound_new_region = tcc_get_symbol_err(s1, "__bound_new_region");
        bound_delete_region = tcc_get_symbol_err(s1, "__bound_delete_region");

        bound_init();
        /* mark argv area as valid */
        bound_new_region(argv, argc*sizeof(argv[0]));
        for (i=0; i<argc; ++i)
            bound_new_region(argv[i], strlen(argv[i]) + 1);

        ret = (*prog_main)(argc, argv);

        /* unmark argv area */
        for (i=0; i<argc; ++i)
            bound_delete_region(argv[i]);
        bound_delete_region(argv);
        bound_exit();
        return ret;
    }
#endif
    return (*prog_main)(argc, argv);
}

#if defined TCC_TARGET_I386 || defined TCC_TARGET_X86_64
 #define RUN_SECTION_ALIGNMENT 63
#else
 #define RUN_SECTION_ALIGNMENT 15
#endif

/* relocate code. Return -1 on error, required size if ptr is NULL,
   otherwise copy code into buffer passed by the caller */
static int tcc_relocate_ex(TCCState *s1, void *ptr, addr_t ptr_diff)
{
    Section *s;
    unsigned offset, length, fill, i, k;
    addr_t mem;

    if (NULL == ptr) {
        s1->nb_errors = 0;
        tcc_add_runtime(s1);
	resolve_common_syms(s1);
        build_got_entries(s1);
        if( s1->nb_errors )  return -1;
    }

    offset = 0, mem = (addr_t)ptr;
    fill = -mem & RUN_SECTION_ALIGNMENT;
    for (k = 0; k < 2; ++k) {
        for(i = 1; i < s1->nb_sections; i++) {
            s = s1->sections[i];
            if (0 == (s->sh_flags & SHF_ALLOC))
                continue;
            if (k != !(s->sh_flags & SHF_EXECINSTR))
                continue;
            offset += fill;
            if (!mem)
                s->sh_addr = 0;
            else if (s->sh_flags & SHF_EXECINSTR)
                s->sh_addr = mem + offset + ptr_diff;
            else
                s->sh_addr = mem + offset;
            offset += s->data_offset;
            fill = -(mem + offset) & 15;
        }
#if RUN_SECTION_ALIGNMENT > 15
        /* To avoid that x86 processors would reload cached instructions each time
           when data is written in the near, we need to make sure that code and data
           do not share the same 64 byte unit */
        fill = -(mem + offset) & RUN_SECTION_ALIGNMENT;
#endif
    }

    /* relocate symbols */
    relocate_syms(s1, s1->symtab, 1);
    if( s1->nb_errors )  return -1;

    if (0 == mem)
        return offset + RUN_SECTION_ALIGNMENT;

    /* relocate each section */
    for(i = 1; i < s1->nb_sections; i++) {
        s = s1->sections[i];
        if (s->reloc)
            relocate_section(s1, s);
    }
    relocate_plt(s1);

    for(i = 1; i < s1->nb_sections; i++) {
        s = s1->sections[i];
        if (0 == (s->sh_flags & SHF_ALLOC))
            continue;
        length = s->data_offset;
        ptr = (void*)s->sh_addr;
        if (s->sh_flags & SHF_EXECINSTR)
            ptr = (char*)ptr - ptr_diff;
        if (NULL == s->data || s->sh_type == SHT_NOBITS)
            memset(ptr, 0, length);
        else
            memcpy(ptr, s->data, length);
        /* mark executable sections as executable in memory */
        if (s->sh_flags & SHF_EXECINSTR)
            set_pages_executable((char*)ptr + ptr_diff, length);
    }
  return 0;
}

/* ------------------------------------------------------------- */
/* allow to run code in memory */

static void set_pages_executable(void *ptr, unsigned long length)
{
    void __clear_cache(void *beginning, void *end);
# ifndef HAVE_SELINUX
    addr_t start, end;
#  ifndef PAGESIZE
#   define PAGESIZE 4096
#  endif
    start = (addr_t)ptr & ~(PAGESIZE - 1);
    end = (addr_t)ptr + length;
    end = (end + PAGESIZE - 1) & ~(PAGESIZE - 1);
    if (mprotect((void *)start, end - start, PROT_READ | PROT_WRITE | PROT_EXEC))
        tcc_error(-1, "mprotect failed: did you mean to configure --with-selinux?");
# endif
# if defined TCC_TARGET_ARM || defined TCC_TARGET_ARM64
    __clear_cache(ptr, (char *)ptr + length);
# endif
}

/* ------------------------------------------------------------- */
#ifdef CONFIG_TCC_BACKTRACE

ST_FUNC void tcc_set_num_callers(int n)
{
    rt_num_callers = n;
}

/* print the position in the source file of PC value 'pc' by reading
   the stabs debug information */
static addr_t rt_printline(addr_t wanted_pc, const char *msg)
{
    char func_name[128], last_func_name[128];
    addr_t func_addr, last_pc, pc;
    const char *incl_files[INCLUDE_STACK_SIZE];
    int incl_index, len, last_line_num, i;
    const char *str, *p;

    Stab_Sym *stab_sym = NULL, *stab_sym_end, *sym;
    int stab_len = 0;
    char *stab_str = NULL;

    if (stab_section) {
        stab_len = stab_section->data_offset;
        stab_sym = (Stab_Sym *)stab_section->data;
        stab_str = (char *) stabstr_section->data;
    }

    func_name[0] = '\0';
    func_addr = 0;
    incl_index = 0;
    last_func_name[0] = '\0';
    last_pc = (addr_t)-1;
    last_line_num = 1;

    if (!stab_sym)
        goto no_stabs;

    stab_sym_end = (Stab_Sym*)((char*)stab_sym + stab_len);
    for (sym = stab_sym + 1; sym < stab_sym_end; ++sym) {
        switch(sym->n_type) {
            /* function start or end */
        case N_FUN:
            if (sym->n_strx == 0) {
                /* we test if between last line and end of function */
                pc = sym->n_value + func_addr;
                if (wanted_pc >= last_pc && wanted_pc < pc)
                    goto found;
                func_name[0] = '\0';
                func_addr = 0;
            } else {
                str = stab_str + sym->n_strx;
                p = strchr(str, ':');
                if (!p) {
                    pstrcpy(func_name, sizeof(func_name), str);
                } else {
                    len = p - str;
                    if (len > sizeof(func_name) - 1)
                        len = sizeof(func_name) - 1;
                    memcpy(func_name, str, len);
                    func_name[len] = '\0';
                }
                func_addr = sym->n_value;
            }
            break;
            /* line number info */
        case N_SLINE:
            pc = sym->n_value + func_addr;
            if (wanted_pc >= last_pc && wanted_pc < pc)
                goto found;
            last_pc = pc;
            last_line_num = sym->n_desc;
            /* XXX: slow! */
            strcpy(last_func_name, func_name);
            break;
            /* include files */
        case N_BINCL:
            str = stab_str + sym->n_strx;
        add_incl:
            if (incl_index < INCLUDE_STACK_SIZE) {
                incl_files[incl_index++] = str;
            }
            break;
        case N_EINCL:
            if (incl_index > 1)
                incl_index--;
            break;
        case N_SO:
            if (sym->n_strx == 0) {
                incl_index = 0; /* end of translation unit */
            } else {
                str = stab_str + sym->n_strx;
                /* do not add path */
                len = strlen(str);
                if (len > 0 && str[len - 1] != '/')
                    goto add_incl;
            }
            break;
        }
    }

no_stabs:
    /* second pass: we try symtab symbols (no line number info) */
    incl_index = 0;
    if (symtab_section)
    {
        ElfW(Sym) *sym, *sym_end;
        int type;

        sym_end = (ElfW(Sym) *)(symtab_section->data + symtab_section->data_offset);
        for(sym = (ElfW(Sym) *)symtab_section->data + 1;
            sym < sym_end;
            sym++) {
            type = ELFW(ST_TYPE)(sym->st_info);
            if (type == STT_FUNC || type == STT_GNU_IFUNC) {
                if (wanted_pc >= sym->st_value &&
                    wanted_pc < sym->st_value + sym->st_size) {
                    pstrcpy(last_func_name, sizeof(last_func_name),
                            (char *) symtab_section->link->data + sym->st_name);
                    func_addr = sym->st_value;
                    goto found;
                }
            }
        }
    }
    /* did not find any info: */
    fprintf(stderr, "%s %p ???\n", msg, (void*)wanted_pc);
    fflush(stderr);
    return 0;
 found:
    i = incl_index;
    if (i > 0)
        fprintf(stderr, "%s:%d: ", incl_files[--i], last_line_num);
    fprintf(stderr, "%s %p", msg, (void*)wanted_pc);
    if (last_func_name[0] != '\0')
        fprintf(stderr, " %s()", last_func_name);
    if (--i >= 0) {
        fprintf(stderr, " (included from ");
        for (;;) {
            fprintf(stderr, "%s", incl_files[i]);
            if (--i < 0)
                break;
            fprintf(stderr, ", ");
        }
        fprintf(stderr, ")");
    }
    fprintf(stderr, "\n");
    fflush(stderr);
    return func_addr;
}

/* emit a run time error at position 'pc' */
static void rt_error(ucontext_t *uc, const char *fmt, ...)
{
    va_list ap;
    addr_t pc;
    int i;

    fprintf(stderr, "Runtime error: ");
    va_start(ap, fmt);
    vfprintf(stderr, fmt, ap);
    va_end(ap);
    fprintf(stderr, "\n");

    for(i=0;i<rt_num_callers;i++) {
        if (rt_get_caller_pc(&pc, uc, i) < 0)
            break;
        pc = rt_printline(pc, i ? "by" : "at");
        if (pc == (addr_t)rt_prog_main && pc)
            break;
    }
}

/* ------------------------------------------------------------- */
#ifndef _WIN32

/* signal handler for fatal errors */
static void sig_error(int signum, siginfo_t *siginf, void *puc)
{
    ucontext_t *uc = puc;

    switch(signum) {
    case SIGFPE:
        switch(siginf->si_code) {
        case FPE_INTDIV:
        case FPE_FLTDIV:
            rt_error(uc, "division by zero");
            break;
        default:
            rt_error(uc, "floating point exception");
            break;
        }
        break;
    case SIGBUS:
    case SIGSEGV:
        if (rt_bound_error_msg && *rt_bound_error_msg)
            rt_error(uc, *rt_bound_error_msg);
        else
            rt_error(uc, "dereferencing invalid pointer");
        break;
    case SIGILL:
        rt_error(uc, "illegal instruction");
        break;
    case SIGABRT:
        rt_error(uc, "abort() called");
        break;
    default:
        rt_error(uc, "caught signal %d", signum);
        break;
    }
    exit( -205 );  // JJX  used to be:   exit(255);
}

#ifndef SA_SIGINFO
# define SA_SIGINFO 0x00000004u
#endif

/* Generate a stack backtrace when a CPU exception occurs. */
static void set_exception_handler(void)
{
    struct sigaction sigact;
    /* install TCC signal handlers to print debug info on fatal
       runtime errors */
    sigact.sa_flags = SA_SIGINFO | SA_RESETHAND;
    sigact.sa_sigaction = sig_error;
    sigemptyset(&sigact.sa_mask);
    sigaction(SIGFPE, &sigact, NULL);
    sigaction(SIGILL, &sigact, NULL);
    sigaction(SIGSEGV, &sigact, NULL);
    sigaction(SIGBUS, &sigact, NULL);
    sigaction(SIGABRT, &sigact, NULL);
}

/* ------------------------------------------------------------- */
#ifdef __i386__

/* fix for glibc 2.1 */
#ifndef REG_EIP
#define REG_EIP EIP
#define REG_EBP EBP
#endif

/* return the PC at frame level 'level'. Return negative if not found */
static int rt_get_caller_pc(addr_t *paddr, ucontext_t *uc, int level)
{
    addr_t fp;
    int i;

    if (level == 0) {
#if defined(__APPLE__)
        *paddr = uc->uc_mcontext->__ss.__eip;
#elif defined(__FreeBSD__) || defined(__FreeBSD_kernel__) || defined(__DragonFly__)
        *paddr = uc->uc_mcontext.mc_eip;
#elif defined(__dietlibc__)
        *paddr = uc->uc_mcontext.eip;
#elif defined(__NetBSD__)
        *paddr = uc->uc_mcontext.__gregs[_REG_EIP];
#elif defined(__OpenBSD__)
        *paddr = uc->sc_eip;
#else
        *paddr = uc->uc_mcontext.gregs[REG_EIP];
#endif
        return 0;
    } else {
#if defined(__APPLE__)
        fp = uc->uc_mcontext->__ss.__ebp;
#elif defined(__FreeBSD__) || defined(__FreeBSD_kernel__) || defined(__DragonFly__)
        fp = uc->uc_mcontext.mc_ebp;
#elif defined(__dietlibc__)
        fp = uc->uc_mcontext.ebp;
#elif defined(__NetBSD__)
        fp = uc->uc_mcontext.__gregs[_REG_EBP];
#elif defined(__OpenBSD__)
        *paddr = uc->sc_ebp;
#else
        fp = uc->uc_mcontext.gregs[REG_EBP];
#endif
        for(i=1;i<level;i++) {
            /* XXX: check address validity with program info */
            if (fp <= 0x1000 || fp >= 0xc0000000)
                return -1;
            fp = ((addr_t *)fp)[0];
        }
        *paddr = ((addr_t *)fp)[1];
        return 0;
    }
}

/* ------------------------------------------------------------- */
#elif defined(__x86_64__)

/* return the PC at frame level 'level'. Return negative if not found */
static int rt_get_caller_pc(addr_t *paddr, ucontext_t *uc, int level)
{
    addr_t fp;
    int i;

    if (level == 0) {
        /* XXX: only support linux */
#if defined(__APPLE__)
        *paddr = uc->uc_mcontext->__ss.__rip;
#elif defined(__FreeBSD__) || defined(__FreeBSD_kernel__) || defined(__DragonFly__)
        *paddr = uc->uc_mcontext.mc_rip;
#elif defined(__NetBSD__)
        *paddr = uc->uc_mcontext.__gregs[_REG_RIP];
#else
        *paddr = uc->uc_mcontext.gregs[REG_RIP];
#endif
        return 0;
    } else {
#if defined(__APPLE__)
        fp = uc->uc_mcontext->__ss.__rbp;
#elif defined(__FreeBSD__) || defined(__FreeBSD_kernel__) || defined(__DragonFly__)
        fp = uc->uc_mcontext.mc_rbp;
#elif defined(__NetBSD__)
        fp = uc->uc_mcontext.__gregs[_REG_RBP];
#else
        fp = uc->uc_mcontext.gregs[REG_RBP];
#endif
        for(i=1;i<level;i++) {
            /* XXX: check address validity with program info */
            if (fp <= 0x1000)
                return -1;
            fp = ((addr_t *)fp)[0];
        }
        *paddr = ((addr_t *)fp)[1];
        return 0;
    }
}

/* ------------------------------------------------------------- */
#elif defined(__arm__)

/* return the PC at frame level 'level'. Return negative if not found */
static int rt_get_caller_pc(addr_t *paddr, ucontext_t *uc, int level)
{
    addr_t fp, sp;
    int i;

    if (level == 0) {
        /* XXX: only supports linux */
#if defined(__linux__)
        *paddr = uc->uc_mcontext.arm_pc;
#else
        return -1;
#endif
        return 0;
    } else {
#if defined(__linux__)
        fp = uc->uc_mcontext.arm_fp;
        sp = uc->uc_mcontext.arm_sp;
        if (sp < 0x1000)
            sp = 0x1000;
#else
        return -1;
#endif
        /* XXX: specific to tinycc stack frames */
        if (fp < sp + 12 || fp & 3)
            return -1;
        for(i = 1; i < level; i++) {
            sp = ((addr_t *)fp)[-2];
            if (sp < fp || sp - fp > 16 || sp & 3)
                return -1;
            fp = ((addr_t *)fp)[-3];
            if (fp <= sp || fp - sp < 12 || fp & 3)
                return -1;
        }
        /* XXX: check address validity with program info */
        *paddr = ((addr_t *)fp)[-1];
        return 0;
    }
}

/* ------------------------------------------------------------- */
#elif defined(__aarch64__)

static int rt_get_caller_pc(addr_t *paddr, ucontext_t *uc, int level)
{
    if (level < 0)
        return -1;
    else if (level == 0) {
        *paddr = uc->uc_mcontext.pc;
        return 0;
    }
    else {
        addr_t *fp = (addr_t *)uc->uc_mcontext.regs[29];
        int i;
        for (i = 1; i < level; i++)
            fp = (addr_t *)fp[0];
        *paddr = fp[1];
        return 0;
    }
}

/* ------------------------------------------------------------- */
#else

#warning add arch specific rt_get_caller_pc()
static int rt_get_caller_pc(addr_t *paddr, ucontext_t *uc, int level)
{
    return -1;
}

#endif /* !__i386__ */

/* ------------------------------------------------------------- */
#else /* WIN32 */

static long __stdcall cpu_exception_handler(EXCEPTION_POINTERS *ex_info)
{
    EXCEPTION_RECORD *er = ex_info->ExceptionRecord;
    CONTEXT *uc = ex_info->ContextRecord;
    switch (er->ExceptionCode) {
    case EXCEPTION_ACCESS_VIOLATION:
        if (rt_bound_error_msg && *rt_bound_error_msg)
            rt_error(uc, *rt_bound_error_msg);
        else
	    rt_error(uc, "access violation");
        break;
    case EXCEPTION_STACK_OVERFLOW:
        rt_error(uc, "stack overflow");
        break;
    case EXCEPTION_INT_DIVIDE_BY_ZERO:
        rt_error(uc, "division by zero");
        break;
    default:
        rt_error(uc, "exception caught");
        break;
    }
    return EXCEPTION_EXECUTE_HANDLER;
}

/* Generate a stack backtrace when a CPU exception occurs. */
static void set_exception_handler(void)
{
    SetUnhandledExceptionFilter(cpu_exception_handler);
}

/* return the PC at frame level 'level'. Return non zero if not found */
static int rt_get_caller_pc(addr_t *paddr, CONTEXT *uc, int level)
{
    addr_t fp, pc;
    int i;
#ifdef _WIN64
    pc = uc->Rip;
    fp = uc->Rbp;
#else
    pc = uc->Eip;
    fp = uc->Ebp;
#endif
    if (level > 0) {
        for(i=1;i<level;i++) {
	    /* XXX: check address validity with program info */
	    if (fp <= 0x1000 || fp >= 0xc0000000)
		return -1;
	    fp = ((addr_t*)fp)[0];
	}
        pc = ((addr_t*)fp)[1];
    }
    *paddr = pc;
    return 0;
}

#endif /* _WIN32 */
#endif /* CONFIG_TCC_BACKTRACE */
/* ------------------------------------------------------------- */
#ifdef CONFIG_TCC_STATIC

/* dummy function for profiling */
ST_FUNC void *dlopen(const char *filename, int flag)
{
    return NULL;
}

ST_FUNC void dlclose(void *p)
{
}

ST_FUNC const char *dlerror(void)
{
    return "error";
}

typedef struct TCCSyms {
    char *str;
    void *ptr;
} TCCSyms;


/* add the symbol you want here if no dynamic linking is done */
static TCCSyms tcc_syms[] = {
#if !defined(CONFIG_TCCBOOT)
#define TCCSYM(a) { #a, &a, },
    TCCSYM(printf)
    TCCSYM(fprintf)
    TCCSYM(fopen)
    TCCSYM(fclose)
#undef TCCSYM
#endif
    { NULL, NULL },
};

ST_FUNC void *dlsym(void *handle, const char *symbol)
{
    TCCSyms *p;
    p = tcc_syms;
    while (p->str != NULL) {
        if (!strcmp(p->str, symbol))
            return p->ptr;
        p++;
    }
    return NULL;
}

#endif /* CONFIG_TCC_STATIC */
#endif /* TCC_IS_NATIVE */
/* ------------------------------------------------------------- */

#ifdef TCC_TARGET_I386

/**  #include "i386-gen.c"  **/

/*  X86 code generator for TCC
 *  Copyright (c) 2001-2004 Fabrice Bellard
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */

/* define to 1/0 to [not] have EBX as 4th register */
#define USE_EBX 0

ST_DATA const int reg_classes[NB_REGS] = {
    /* eax */ RC_INT | RC_EAX,
    /* ecx */ RC_INT | RC_ECX,
    /* edx */ RC_INT | RC_EDX,
    /* ebx */ (RC_INT | RC_EBX) * USE_EBX,
    /* st0 */ RC_FLOAT | RC_ST0,
};

static unsigned long func_sub_sp_offset;
static int func_ret_sub;
#ifdef CONFIG_TCC_BCHECK
static addr_t func_bound_offset;
static unsigned long func_bound_ind;
#endif

/* XXX: make it faster ? */
ST_FUNC void g(int c)
{
    int ind1;
    if (nocode_wanted)
        return;
    ind1 = ind + 1;
    if (ind1 > cur_text_section->data_allocated)
        section_realloc(cur_text_section, ind1);
    cur_text_section->data[ind] = c;
    ind = ind1;
}

ST_FUNC void o(unsigned int c)
{
    while (c) {
        g(c);
        c = c >> 8;
    }
}

ST_FUNC void gen_le16(int v)
{
    g(v);
    g(v >> 8);
}

ST_FUNC void gen_le32(int c)
{
    g(c);
    g(c >> 8);
    g(c >> 16);
    g(c >> 24);
}

/* output a symbol and patch all calls to it */
ST_FUNC void gsym_addr(int t, int a)
{
    while (t) {
        unsigned char *ptr = cur_text_section->data + t;
        uint32_t n = read32le(ptr); /* next value */
        write32le(ptr, a - t - 4);
        t = n;
    }
}

ST_FUNC void gsym(int t)
{
    gsym_addr(t, ind);
}

/* instruction + 4 bytes data. Return the address of the data */
static int oad(int c, int s)
{
    int t;
    if (nocode_wanted)
        return s;
    o(c);
    t = ind;
    gen_le32(s);
    return t;
}

/* generate jmp to a label */
#define gjmp2(instr,lbl) oad(instr,lbl)

/* output constant with relocation if 'r & VT_SYM' is true */
ST_FUNC void gen_addr32(int r, Sym *sym, int c)
{
    if (r & VT_SYM)
        greloc(cur_text_section, sym, ind, R_386_32);
    gen_le32(c);
}

ST_FUNC void gen_addrpc32(int r, Sym *sym, int c)
{
    if (r & VT_SYM)
        greloc(cur_text_section, sym, ind, R_386_PC32);
    gen_le32(c - 4);
}

/* generate a modrm reference. 'op_reg' contains the additional 3
   opcode bits */
static void gen_modrm(int op_reg, int r, Sym *sym, int c)
{
    op_reg = op_reg << 3;
    if ((r & VT_VALMASK) == VT_CONST) {
        /* constant memory reference */
        o(0x05 | op_reg);
        gen_addr32(r, sym, c);
    } else if ((r & VT_VALMASK) == VT_LOCAL) {
        /* currently, we use only ebp as base */
        if (c == (char)c) {
            /* short reference */
            o(0x45 | op_reg);
            g(c);
        } else {
            oad(0x85 | op_reg, c);
        }
    } else {
        g(0x00 | op_reg | (r & VT_VALMASK));
    }
}

/* load 'r' from value 'sv' */
ST_FUNC void load(int r, SValue *sv)
{
    int v, t, ft, fc, fr;
    SValue v1;

#ifdef TCC_TARGET_PE
    SValue v2;
    sv = pe_getimport(sv, &v2);
#endif

    fr = sv->r;
    ft = sv->type.t & ~VT_DEFSIGN;
    fc = sv->c.i;

    ft &= ~(VT_VOLATILE | VT_CONSTANT);

    v = fr & VT_VALMASK;
    if (fr & VT_LVAL) {
        if (v == VT_LLOCAL) {
            v1.type.t = VT_INT;
            v1.r = VT_LOCAL | VT_LVAL;
            v1.c.i = fc;
            fr = r;
            if (!(reg_classes[fr] & RC_INT))
                fr = get_reg(RC_INT);
            load(fr, &v1);
        }
        if ((ft & VT_BTYPE) == VT_FLOAT) {
            o(0xd9); /* flds */
            r = 0;
        } else if ((ft & VT_BTYPE) == VT_DOUBLE) {
            o(0xdd); /* fldl */
            r = 0;
        } else if ((ft & VT_BTYPE) == VT_LDOUBLE) {
            o(0xdb); /* fldt */
            r = 5;
        } else if ((ft & VT_TYPE) == VT_BYTE || (ft & VT_TYPE) == VT_BOOL) {
            o(0xbe0f);   /* movsbl */
        } else if ((ft & VT_TYPE) == (VT_BYTE | VT_UNSIGNED)) {
            o(0xb60f);   /* movzbl */
        } else if ((ft & VT_TYPE) == VT_SHORT) {
            o(0xbf0f);   /* movswl */
        } else if ((ft & VT_TYPE) == (VT_SHORT | VT_UNSIGNED)) {
            o(0xb70f);   /* movzwl */
        } else {
            o(0x8b);     /* movl */
        }
        gen_modrm(r, fr, sv->sym, fc);
    } else {
        if (v == VT_CONST) {
            o(0xb8 + r); /* mov $xx, r */
            gen_addr32(fr, sv->sym, fc);
        } else if (v == VT_LOCAL) {
            if (fc) {
                o(0x8d); /* lea xxx(%ebp), r */
                gen_modrm(r, VT_LOCAL, sv->sym, fc);
            } else {
                o(0x89);
                o(0xe8 + r); /* mov %ebp, r */
            }
        } else if (v == VT_CMP) {
            oad(0xb8 + r, 0); /* mov $0, r */
            o(0x0f); /* setxx %br */
            o(fc);
            o(0xc0 + r);
        } else if (v == VT_JMP || v == VT_JMPI) {
            t = v & 1;
            oad(0xb8 + r, t); /* mov $1, r */
            o(0x05eb); /* jmp after */
            gsym(fc);
            oad(0xb8 + r, t ^ 1); /* mov $0, r */
        } else if (v != r) {
            o(0x89);
            o(0xc0 + r + v * 8); /* mov v, r */
        }
    }
}

/* store register 'r' in lvalue 'v' */
ST_FUNC void store(int r, SValue *v)
{
    int fr, bt, ft, fc;

#ifdef TCC_TARGET_PE
    SValue v2;
    v = pe_getimport(v, &v2);
#endif

    ft = v->type.t;
    fc = v->c.i;
    fr = v->r & VT_VALMASK;
    ft &= ~(VT_VOLATILE | VT_CONSTANT);
    bt = ft & VT_BTYPE;
    /* XXX: incorrect if float reg to reg */
    if (bt == VT_FLOAT) {
        o(0xd9); /* fsts */
        r = 2;
    } else if (bt == VT_DOUBLE) {
        o(0xdd); /* fstpl */
        r = 2;
    } else if (bt == VT_LDOUBLE) {
        o(0xc0d9); /* fld %st(0) */
        o(0xdb); /* fstpt */
        r = 7;
    } else {
        if (bt == VT_SHORT)
            o(0x66);
        if (bt == VT_BYTE || bt == VT_BOOL)
            o(0x88);
        else
            o(0x89);
    }
    if (fr == VT_CONST ||
        fr == VT_LOCAL ||
        (v->r & VT_LVAL)) {
        gen_modrm(r, v->r, v->sym, fc);
    } else if (fr != r) {
        o(0xc0 + fr + r * 8); /* mov r, fr */
    }
}

static void gadd_sp(int val)
{
    if (val == (char)val) {
        o(0xc483);
        g(val);
    } else {
        oad(0xc481, val); /* add $xxx, %esp */
    }
}

#if defined CONFIG_TCC_BCHECK || defined TCC_TARGET_PE
static void gen_static_call(int v)
{
    Sym *sym;

    sym = external_global_sym(v, &func_old_type, 0);
    oad(0xe8, -4);
    greloc(cur_text_section, sym, ind-4, R_386_PC32);
}
#endif

/* 'is_jmp' is '1' if it is a jump */
static void gcall_or_jmp(int is_jmp)
{
    int r;
    if ((vtop->r & (VT_VALMASK | VT_LVAL)) == VT_CONST && (vtop->r & VT_SYM)) {
        /* constant and relocation case */
        greloc(cur_text_section, vtop->sym, ind + 1, R_386_PC32);
        oad(0xe8 + is_jmp, vtop->c.i - 4); /* call/jmp im */
    } else {
        /* otherwise, indirect call */
        r = gv(RC_INT);
        o(0xff); /* call/jmp *r */
        o(0xd0 + r + (is_jmp << 4));
    }
    if (!is_jmp) {
        int rt;
        /* extend the return value to the whole register if necessary
           visual studio and gcc do not always set the whole eax register
           when assigning the return value of a function  */
        rt = vtop->type.ref->type.t;
        switch (rt & VT_BTYPE) {
            case VT_BYTE:
                if (rt & VT_UNSIGNED) {
                    o(0xc0b60f); /* movzx %al, %eax */
                }
                else {
                    o(0xc0be0f); /* movsx %al, %eax */
                }
                break;
            case VT_SHORT:
                if (rt & VT_UNSIGNED) {
                    o(0xc0b70f); /* movzx %ax, %eax */
                }
                else {
                    o(0xc0bf0f); /* movsx %ax, %eax */
                }
                break;
            default:
                break;
        }
    }
}

static uint8_t fastcall_regs[3] = { TREG_EAX, TREG_EDX, TREG_ECX };
static uint8_t fastcallw_regs[2] = { TREG_ECX, TREG_EDX };

/* Return the number of registers needed to return the struct, or 0 if
   returning via struct pointer. */
ST_FUNC int gfunc_sret(CType *vt, int variadic, CType *ret, int *ret_align, int *regsize)
{
#ifdef TCC_TARGET_PE
    int size, align;
    *ret_align = 1; // Never have to re-align return values for x86
    *regsize = 4;
    size = type_size(vt, &align);
    if (size > 8 || (size & (size - 1)))
        return 0;
    if (size == 8)
        ret->t = VT_LLONG;
    else if (size == 4)
        ret->t = VT_INT;
    else if (size == 2)
        ret->t = VT_SHORT;
    else
        ret->t = VT_BYTE;
    ret->ref = NULL;
    return 1;
#else
    *ret_align = 1; // Never have to re-align return values for x86
    return 0;
#endif
}

/* Generate function call. The function address is pushed first, then
   all the parameters in call order. This functions pops all the
   parameters and the function address. */
ST_FUNC void gfunc_call(int nb_args)
{
    int size, align, r, args_size, i, func_call;
    Sym *func_sym;
    
    args_size = 0;
    for(i = 0;i < nb_args; i++) {
        if ((vtop->type.t & VT_BTYPE) == VT_STRUCT) {
            size = type_size(&vtop->type, &align);
            /* align to stack align size */
            size = (size + 3) & ~3;
            /* allocate the necessary size on stack */
            oad(0xec81, size); /* sub $xxx, %esp */
            /* generate structure store */
            r = get_reg(RC_INT);
            o(0x89); /* mov %esp, r */
            o(0xe0 + r);
            vset(&vtop->type, r | VT_LVAL, 0);
            vswap();
            vstore();
            args_size += size;
        } else if (is_float(vtop->type.t)) {
            gv(RC_FLOAT); /* only one float register */
            if ((vtop->type.t & VT_BTYPE) == VT_FLOAT)
                size = 4;
            else if ((vtop->type.t & VT_BTYPE) == VT_DOUBLE)
                size = 8;
            else
                size = 12;
            oad(0xec81, size); /* sub $xxx, %esp */
            if (size == 12)
                o(0x7cdb);
            else
                o(0x5cd9 + size - 4); /* fstp[s|l] 0(%esp) */
            g(0x24);
            g(0x00);
            args_size += size;
        } else {
            /* simple type (currently always same size) */
            /* XXX: implicit cast ? */
            r = gv(RC_INT);
            if ((vtop->type.t & VT_BTYPE) == VT_LLONG) {
                size = 8;
                o(0x50 + vtop->r2); /* push r */
            } else {
                size = 4;
            }
            o(0x50 + r); /* push r */
            args_size += size;
        }
        vtop--;
    }
    save_regs(0); /* save used temporary registers */
    func_sym = vtop->type.ref;
    func_call = func_sym->f.func_call;
    /* fast call case */
    if ((func_call >= FUNC_FASTCALL1 && func_call <= FUNC_FASTCALL3) ||
        func_call == FUNC_FASTCALLW) {
        int fastcall_nb_regs;
        uint8_t *fastcall_regs_ptr;
        if (func_call == FUNC_FASTCALLW) {
            fastcall_regs_ptr = fastcallw_regs;
            fastcall_nb_regs = 2;
        } else {
            fastcall_regs_ptr = fastcall_regs;
            fastcall_nb_regs = func_call - FUNC_FASTCALL1 + 1;
        }
        for(i = 0;i < fastcall_nb_regs; i++) {
            if (args_size <= 0)
                break;
            o(0x58 + fastcall_regs_ptr[i]); /* pop r */
            /* XXX: incorrect for struct/floats */
            args_size -= 4;
        }
    }
#ifndef TCC_TARGET_PE
    else if ((vtop->type.ref->type.t & VT_BTYPE) == VT_STRUCT)
        args_size -= 4;
#endif
    gcall_or_jmp(0);

    if (args_size && func_call != FUNC_STDCALL && func_call != FUNC_FASTCALLW)
        gadd_sp(args_size);
    vtop--;
}

#ifdef TCC_TARGET_PE
#define FUNC_PROLOG_SIZE (10 + USE_EBX)
#else
#define FUNC_PROLOG_SIZE (9 + USE_EBX)
#endif

/* generate function prolog of type 't' */
ST_FUNC void gfunc_prolog(CType *func_type)
{
    int addr, align, size, func_call, fastcall_nb_regs;
    int param_index, param_addr;
    uint8_t *fastcall_regs_ptr;
    Sym *sym;
    CType *type;

    sym = func_type->ref;
    func_call = sym->f.func_call;
    addr = 8;
    loc = 0;
    func_vc = 0;

    if (func_call >= FUNC_FASTCALL1 && func_call <= FUNC_FASTCALL3) {
        fastcall_nb_regs = func_call - FUNC_FASTCALL1 + 1;
        fastcall_regs_ptr = fastcall_regs;
    } else if (func_call == FUNC_FASTCALLW) {
        fastcall_nb_regs = 2;
        fastcall_regs_ptr = fastcallw_regs;
    } else {
        fastcall_nb_regs = 0;
        fastcall_regs_ptr = NULL;
    }
    param_index = 0;

    ind += FUNC_PROLOG_SIZE;
    func_sub_sp_offset = ind;
    /* if the function returns a structure, then add an
       implicit pointer parameter */
    func_vt = sym->type;
    func_var = (sym->f.func_type == FUNC_ELLIPSIS);
#ifdef TCC_TARGET_PE
    size = type_size(&func_vt,&align);
    if (((func_vt.t & VT_BTYPE) == VT_STRUCT)
        && (size > 8 || (size & (size - 1)))) {
#else
    if ((func_vt.t & VT_BTYPE) == VT_STRUCT) {
#endif
        /* XXX: fastcall case ? */
        func_vc = addr;
        addr += 4;
        param_index++;
    }
    /* define parameters */
    while ((sym = sym->next) != NULL) {
        type = &sym->type;
        size = type_size(type, &align);
        size = (size + 3) & ~3;
#ifdef FUNC_STRUCT_PARAM_AS_PTR
        /* structs are passed as pointer */
        if ((type->t & VT_BTYPE) == VT_STRUCT) {
            size = 4;
        }
#endif
        if (param_index < fastcall_nb_regs) {
            /* save FASTCALL register */
            loc -= 4;
            o(0x89);     /* movl */
            gen_modrm(fastcall_regs_ptr[param_index], VT_LOCAL, NULL, loc);
            param_addr = loc;
        } else {
            param_addr = addr;
            addr += size;
        }
        sym_push(sym->v & ~SYM_FIELD, type,
                 VT_LOCAL | lvalue_type(type->t), param_addr);
        param_index++;
    }
    func_ret_sub = 0;
    /* pascal type call or fastcall ? */
    if (func_call == FUNC_STDCALL || func_call == FUNC_FASTCALLW)
        func_ret_sub = addr - 8;
#ifndef TCC_TARGET_PE
    else if (func_vc)
        func_ret_sub = 4;
#endif

#ifdef CONFIG_TCC_BCHECK
    /* leave some room for bound checking code */
    if (tcc_state->do_bounds_check) {
        func_bound_offset = lbounds_section->data_offset;
        func_bound_ind = ind;
        oad(0xb8, 0); /* lbound section pointer */
        oad(0xb8, 0); /* call to function */
    }
#endif
}

/* generate function epilog */
ST_FUNC void gfunc_epilog(void)
{
    addr_t v, saved_ind;

#ifdef CONFIG_TCC_BCHECK
    if (tcc_state->do_bounds_check
     && func_bound_offset != lbounds_section->data_offset) {
        addr_t saved_ind;
        addr_t *bounds_ptr;
        Sym *sym_data;

        /* add end of table info */
        bounds_ptr = section_ptr_add(lbounds_section, sizeof(addr_t));
        *bounds_ptr = 0;

        /* generate bound local allocation */
        saved_ind = ind;
        ind = func_bound_ind;
        sym_data = get_sym_ref(&char_pointer_type, lbounds_section, 
                               func_bound_offset, lbounds_section->data_offset);
        greloc(cur_text_section, sym_data,
               ind + 1, R_386_32);
        oad(0xb8, 0); /* mov %eax, xxx */
        gen_static_call(TOK___bound_local_new);
        ind = saved_ind;

        /* generate bound check local freeing */
        o(0x5250); /* save returned value, if any */
        greloc(cur_text_section, sym_data, ind + 1, R_386_32);
        oad(0xb8, 0); /* mov %eax, xxx */
        gen_static_call(TOK___bound_local_delete);
        o(0x585a); /* restore returned value, if any */
    }
#endif

    /* align local size to word & save local variables */
    v = (-loc + 3) & -4;

#if USE_EBX
    o(0x8b);
    gen_modrm(TREG_EBX, VT_LOCAL, NULL, -(v+4));
#endif

    o(0xc9); /* leave */
    if (func_ret_sub == 0) {
        o(0xc3); /* ret */
    } else {
        o(0xc2); /* ret n */
        g(func_ret_sub);
        g(func_ret_sub >> 8);
    }
    saved_ind = ind;
    ind = func_sub_sp_offset - FUNC_PROLOG_SIZE;
#ifdef TCC_TARGET_PE
    if (v >= 4096) {
        oad(0xb8, v); /* mov stacksize, %eax */
        gen_static_call(TOK___chkstk); /* call __chkstk, (does the stackframe too) */
    } else
#endif
    {
        o(0xe58955);  /* push %ebp, mov %esp, %ebp */
        o(0xec81);  /* sub esp, stacksize */
        gen_le32(v);
#ifdef TCC_TARGET_PE
        o(0x90);  /* adjust to FUNC_PROLOG_SIZE */
#endif
    }
    o(0x53 * USE_EBX); /* push ebx */
    ind = saved_ind;
}

/* generate a jump to a label */
ST_FUNC int gjmp(int t)
{
    return gjmp2(0xe9, t);
}

/* generate a jump to a fixed address */
ST_FUNC void gjmp_addr(int a)
{
    int r;
    r = a - ind - 2;
    if (r == (char)r) {
        g(0xeb);
        g(r);
    } else {
        oad(0xe9, a - ind - 5);
    }
}

ST_FUNC void gtst_addr(int inv, int a)
{
    int v = vtop->r & VT_VALMASK;
    if (v == VT_CMP) {
	inv ^= (vtop--)->c.i;
	a -= ind + 2;
	if (a == (char)a) {
	    g(inv - 32);
	    g(a);
	} else {
	    g(0x0f);
	    oad(inv - 16, a - 4);
	}
    } else if ((v & ~1) == VT_JMP) {
	if ((v & 1) != inv) {
	    gjmp_addr(a);
	    gsym(vtop->c.i);
	} else {
	    gsym(vtop->c.i);
	    o(0x05eb);
	    gjmp_addr(a);
	}
	vtop--;
    }
}

/* generate a test. set 'inv' to invert test. Stack entry is popped */
ST_FUNC int gtst(int inv, int t)
{
    int v = vtop->r & VT_VALMASK;
    if (nocode_wanted) {
        ;
    } else if (v == VT_CMP) {
        /* fast case : can jump directly since flags are set */
        g(0x0f);
        t = gjmp2((vtop->c.i - 16) ^ inv, t);
    } else if (v == VT_JMP || v == VT_JMPI) {
        /* && or || optimization */
        if ((v & 1) == inv) {
            /* insert vtop->c jump list in t */
            uint32_t n1, n = vtop->c.i;
            if (n) {
                while ((n1 = read32le(cur_text_section->data + n)))
                    n = n1;
                write32le(cur_text_section->data + n, t);
                t = vtop->c.i;
            }
        } else {
            t = gjmp(t);
            gsym(vtop->c.i);
        }
    }
    vtop--;
    return t;
}

/* generate an integer binary operation */
ST_FUNC void gen_opi(int op)
{
    int r, fr, opc, c;

    switch(op) {
    case '+':
    case TOK_ADDC1: /* add with carry generation */
        opc = 0;
    gen_op8:
        if ((vtop->r & (VT_VALMASK | VT_LVAL | VT_SYM)) == VT_CONST) {
            /* constant case */
            vswap();
            r = gv(RC_INT);
            vswap();
            c = vtop->c.i;
            if (c == (char)c) {
                /* generate inc and dec for smaller code */
                if (c==1 && opc==0 && op != TOK_ADDC1) {
                    o (0x40 | r); // inc
                } else if (c==1 && opc==5 && op != TOK_SUBC1) {
                    o (0x48 | r); // dec
                } else {
                    o(0x83);
                    o(0xc0 | (opc << 3) | r);
                    g(c);
                }
            } else {
                o(0x81);
                oad(0xc0 | (opc << 3) | r, c);
            }
        } else {
            gv2(RC_INT, RC_INT);
            r = vtop[-1].r;
            fr = vtop[0].r;
            o((opc << 3) | 0x01);
            o(0xc0 + r + fr * 8); 
        }
        vtop--;
        if (op >= TOK_ULT && op <= TOK_GT) {
            vtop->r = VT_CMP;
            vtop->c.i = op;
        }
        break;
    case '-':
    case TOK_SUBC1: /* sub with carry generation */
        opc = 5;
        goto gen_op8;
    case TOK_ADDC2: /* add with carry use */
        opc = 2;
        goto gen_op8;
    case TOK_SUBC2: /* sub with carry use */
        opc = 3;
        goto gen_op8;
    case '&':
        opc = 4;
        goto gen_op8;
    case '^':
        opc = 6;
        goto gen_op8;
    case '|':
        opc = 1;
        goto gen_op8;
    case '*':
        gv2(RC_INT, RC_INT);
        r = vtop[-1].r;
        fr = vtop[0].r;
        vtop--;
        o(0xaf0f); /* imul fr, r */
        o(0xc0 + fr + r * 8);
        break;
    case TOK_SHL:
        opc = 4;
        goto gen_shift;
    case TOK_SHR:
        opc = 5;
        goto gen_shift;
    case TOK_SAR:
        opc = 7;
    gen_shift:
        opc = 0xc0 | (opc << 3);
        if ((vtop->r & (VT_VALMASK | VT_LVAL | VT_SYM)) == VT_CONST) {
            /* constant case */
            vswap();
            r = gv(RC_INT);
            vswap();
            c = vtop->c.i & 0x1f;
            o(0xc1); /* shl/shr/sar $xxx, r */
            o(opc | r);
            g(c);
        } else {
            /* we generate the shift in ecx */
            gv2(RC_INT, RC_ECX);
            r = vtop[-1].r;
            o(0xd3); /* shl/shr/sar %cl, r */
            o(opc | r);
        }
        vtop--;
        break;
    case '/':
    case TOK_UDIV:
    case TOK_PDIV:
    case '%':
    case TOK_UMOD:
    case TOK_UMULL:
        /* first operand must be in eax */
        /* XXX: need better constraint for second operand */
        gv2(RC_EAX, RC_ECX);
        r = vtop[-1].r;
        fr = vtop[0].r;
        vtop--;
        save_reg(TREG_EDX);
        /* save EAX too if used otherwise */
        save_reg_upstack(TREG_EAX, 1);
        if (op == TOK_UMULL) {
            o(0xf7); /* mul fr */
            o(0xe0 + fr);
            vtop->r2 = TREG_EDX;
            r = TREG_EAX;
        } else {
            if (op == TOK_UDIV || op == TOK_UMOD) {
                o(0xf7d231); /* xor %edx, %edx, div fr, %eax */
                o(0xf0 + fr);
            } else {
                o(0xf799); /* cltd, idiv fr, %eax */
                o(0xf8 + fr);
            }
            if (op == '%' || op == TOK_UMOD)
                r = TREG_EDX;
            else
                r = TREG_EAX;
        }
        vtop->r = r;
        break;
    default:
        opc = 7;
        goto gen_op8;
    }
}

/* generate a floating point operation 'v = t1 op t2' instruction. The
   two operands are guaranteed to have the same floating point type */
/* XXX: need to use ST1 too */
ST_FUNC void gen_opf(int op)
{
    int a, ft, fc, swapped, r;

    /* convert constants to memory references */
    if ((vtop[-1].r & (VT_VALMASK | VT_LVAL)) == VT_CONST) {
        vswap();
        gv(RC_FLOAT);
        vswap();
    }
    if ((vtop[0].r & (VT_VALMASK | VT_LVAL)) == VT_CONST)
        gv(RC_FLOAT);

    /* must put at least one value in the floating point register */
    if ((vtop[-1].r & VT_LVAL) &&
        (vtop[0].r & VT_LVAL)) {
        vswap();
        gv(RC_FLOAT);
        vswap();
    }
    swapped = 0;
    /* swap the stack if needed so that t1 is the register and t2 is
       the memory reference */
    if (vtop[-1].r & VT_LVAL) {
        vswap();
        swapped = 1;
    }
    if (op >= TOK_ULT && op <= TOK_GT) {
        /* load on stack second operand */
        load(TREG_ST0, vtop);
        save_reg(TREG_EAX); /* eax is used by FP comparison code */
        if (op == TOK_GE || op == TOK_GT)
            swapped = !swapped;
        else if (op == TOK_EQ || op == TOK_NE)
            swapped = 0;
        if (swapped)
            o(0xc9d9); /* fxch %st(1) */
        if (op == TOK_EQ || op == TOK_NE)
            o(0xe9da); /* fucompp */
        else
            o(0xd9de); /* fcompp */
        o(0xe0df); /* fnstsw %ax */
        if (op == TOK_EQ) {
            o(0x45e480); /* and $0x45, %ah */
            o(0x40fC80); /* cmp $0x40, %ah */
        } else if (op == TOK_NE) {
            o(0x45e480); /* and $0x45, %ah */
            o(0x40f480); /* xor $0x40, %ah */
            op = TOK_NE;
        } else if (op == TOK_GE || op == TOK_LE) {
            o(0x05c4f6); /* test $0x05, %ah */
            op = TOK_EQ;
        } else {
            o(0x45c4f6); /* test $0x45, %ah */
            op = TOK_EQ;
        }
        vtop--;
        vtop->r = VT_CMP;
        vtop->c.i = op;
    } else {
        /* no memory reference possible for long double operations */
        if ((vtop->type.t & VT_BTYPE) == VT_LDOUBLE) {
            load(TREG_ST0, vtop);
            swapped = !swapped;
        }
        
        switch(op) {
        default:
        case '+':
            a = 0;
            break;
        case '-':
            a = 4;
            if (swapped)
                a++;
            break;
        case '*':
            a = 1;
            break;
        case '/':
            a = 6;
            if (swapped)
                a++;
            break;
        }
        ft = vtop->type.t;
        fc = vtop->c.i;
        if ((ft & VT_BTYPE) == VT_LDOUBLE) {
            o(0xde); /* fxxxp %st, %st(1) */
            o(0xc1 + (a << 3));
        } else {
            /* if saved lvalue, then we must reload it */
            r = vtop->r;
            if ((r & VT_VALMASK) == VT_LLOCAL) {
                SValue v1;
                r = get_reg(RC_INT);
                v1.type.t = VT_INT;
                v1.r = VT_LOCAL | VT_LVAL;
                v1.c.i = fc;
                load(r, &v1);
                fc = 0;
            }

            if ((ft & VT_BTYPE) == VT_DOUBLE)
                o(0xdc);
            else
                o(0xd8);
            gen_modrm(a, r, vtop->sym, fc);
        }
        vtop--;
    }
}

/* convert integers to fp 't' type. Must handle 'int', 'unsigned int'
   and 'long long' cases. */
ST_FUNC void gen_cvt_itof(int t)
{
    save_reg(TREG_ST0);
    gv(RC_INT);
    if ((vtop->type.t & VT_BTYPE) == VT_LLONG) {
        /* signed long long to float/double/long double (unsigned case
           is handled generically) */
        o(0x50 + vtop->r2); /* push r2 */
        o(0x50 + (vtop->r & VT_VALMASK)); /* push r */
        o(0x242cdf); /* fildll (%esp) */
        o(0x08c483); /* add $8, %esp */
    } else if ((vtop->type.t & (VT_BTYPE | VT_UNSIGNED)) == 
               (VT_INT | VT_UNSIGNED)) {
        /* unsigned int to float/double/long double */
        o(0x6a); /* push $0 */
        g(0x00);
        o(0x50 + (vtop->r & VT_VALMASK)); /* push r */
        o(0x242cdf); /* fildll (%esp) */
        o(0x08c483); /* add $8, %esp */
    } else {
        /* int to float/double/long double */
        o(0x50 + (vtop->r & VT_VALMASK)); /* push r */
        o(0x2404db); /* fildl (%esp) */
        o(0x04c483); /* add $4, %esp */
    }
    vtop->r = TREG_ST0;
}

/* convert fp to int 't' type */
ST_FUNC void gen_cvt_ftoi(int t)
{
    int bt = vtop->type.t & VT_BTYPE;
    if (bt == VT_FLOAT)
        vpush_global_sym(&func_old_type, TOK___fixsfdi);
    else if (bt == VT_LDOUBLE)
        vpush_global_sym(&func_old_type, TOK___fixxfdi);
    else
        vpush_global_sym(&func_old_type, TOK___fixdfdi);
    vswap();
    gfunc_call(1);
    vpushi(0);
    vtop->r = REG_IRET;
    vtop->r2 = REG_LRET;
}

/* convert from one floating point type to another */
ST_FUNC void gen_cvt_ftof(int t)
{
    /* all we have to do on i386 is to put the float in a register */
    gv(RC_FLOAT);
}

/* computed goto support */
ST_FUNC void ggoto(void)
{
    gcall_or_jmp(1);
    vtop--;
}

/* bound check support functions */
#ifdef CONFIG_TCC_BCHECK

/* generate a bounded pointer addition */
ST_FUNC void gen_bounded_ptr_add(void)
{
    /* prepare fast i386 function call (args in eax and edx) */
    gv2(RC_EAX, RC_EDX);
    /* save all temporary registers */
    vtop -= 2;
    save_regs(0);
    /* do a fast function call */
    gen_static_call(TOK___bound_ptr_add);
    /* returned pointer is in eax */
    vtop++;
    vtop->r = TREG_EAX | VT_BOUNDED;
    /* address of bounding function call point */
    vtop->c.i = (cur_text_section->reloc->data_offset - sizeof(Elf32_Rel));
}

/* patch pointer addition in vtop so that pointer dereferencing is
   also tested */
ST_FUNC void gen_bounded_ptr_deref(void)
{
    addr_t func;
    int  size, align;
    Elf32_Rel *rel;
    Sym *sym;

    size = 0;
    /* XXX: put that code in generic part of tcc */
    if (!is_float(vtop->type.t)) {
        if (vtop->r & VT_LVAL_BYTE)
            size = 1;
        else if (vtop->r & VT_LVAL_SHORT)
            size = 2;
    }
    if (!size)
        size = type_size(&vtop->type, &align);
    switch(size) {
    case  1: func = TOK___bound_ptr_indir1; break;
    case  2: func = TOK___bound_ptr_indir2; break;
    case  4: func = TOK___bound_ptr_indir4; break;
    case  8: func = TOK___bound_ptr_indir8; break;
    case 12: func = TOK___bound_ptr_indir12; break;
    case 16: func = TOK___bound_ptr_indir16; break;
    default:
        tcc_error(-1, "unhandled size when dereferencing bounded pointer");
        func = 0;
        break;
    }

    /* patch relocation */
    /* XXX: find a better solution ? */
    rel = (Elf32_Rel *)(cur_text_section->reloc->data + vtop->c.i);
    sym = external_global_sym(func, &func_old_type, 0);
    if (!sym->c)
        put_extern_sym(sym, NULL, 0, 0);
    rel->r_info = ELF32_R_INFO(sym->c, ELF32_R_TYPE(rel->r_info));
}
#endif

/* Save the stack pointer onto the stack */
ST_FUNC void gen_vla_sp_save(int addr) {
    /* mov %esp,addr(%ebp)*/
    o(0x89);
    gen_modrm(TREG_ESP, VT_LOCAL, NULL, addr);
}

/* Restore the SP from a location on the stack */
ST_FUNC void gen_vla_sp_restore(int addr) {
    o(0x8b);
    gen_modrm(TREG_ESP, VT_LOCAL, NULL, addr);
}

/* Subtract from the stack pointer, and push the resulting value onto the stack */
ST_FUNC void gen_vla_alloc(CType *type, int align) {
#ifdef TCC_TARGET_PE
    /* alloca does more than just adjust %rsp on Windows */
    vpush_global_sym(&func_old_type, TOK_alloca);
    vswap(); /* Move alloca ref past allocation size */
    gfunc_call(1);
#else
    int r;
    r = gv(RC_INT); /* allocation size */
    /* sub r,%rsp */
    o(0x2b);
    o(0xe0 | r);
    /* We align to 16 bytes rather than align */
    /* and ~15, %esp */
    o(0xf0e483);
    vpop();
#endif
}

/* end of X86 code generator */
/*************************************************************/

/**  #include "i386-link.c"  **/

/* Returns 1 for a code relocation, 0 for a data relocation. For unknown
   relocations, returns -1. */
int code_reloc (int reloc_type)
{
    switch (reloc_type) {
	case R_386_RELATIVE:
	case R_386_16:
        case R_386_32:
	case R_386_GOTPC:
	case R_386_GOTOFF:
	case R_386_GOT32:
	case R_386_GOT32X:
	case R_386_GLOB_DAT:
	case R_386_COPY:
            return 0;

	case R_386_PC16:
	case R_386_PC32:
	case R_386_PLT32:
	case R_386_JMP_SLOT:
            return 1;
    }

    tcc_error(-1, "Unknown relocation type: %d", reloc_type);
    return -1;
}

/* Returns an enumerator to describe whether and when the relocation needs a
   GOT and/or PLT entry to be created. See tcc.h for a description of the
   different values. */
int gotplt_entry_type (int reloc_type)
{
    switch (reloc_type) {
	case R_386_RELATIVE:
	case R_386_16:
	case R_386_GLOB_DAT:
	case R_386_JMP_SLOT:
	case R_386_COPY:
            return NO_GOTPLT_ENTRY;

        case R_386_32:
	    /* This relocations shouldn't normally need GOT or PLT
	       slots if it weren't for simplicity in the code generator.
	       See our caller for comments.  */
            return AUTO_GOTPLT_ENTRY;

	case R_386_PC16:
	case R_386_PC32:
            return AUTO_GOTPLT_ENTRY;

	case R_386_GOTPC:
	case R_386_GOTOFF:
            return BUILD_GOT_ONLY;

	case R_386_GOT32:
	case R_386_GOT32X:
	case R_386_PLT32:
            return ALWAYS_GOTPLT_ENTRY;
    }

    tcc_error(-1, "Unknown relocation type: %d", reloc_type);
    return -1;
}

ST_FUNC unsigned create_plt_entry(TCCState *s1, unsigned got_offset, struct sym_attr *attr)
{
    Section *plt = s1->plt;
    uint8_t *p;
    int modrm;
    unsigned plt_offset, relofs;

    /* on i386 if we build a DLL, we add a %ebx offset */
    if (s1->output_type == TCC_OUTPUT_DLL)
        modrm = 0xa3;
    else
        modrm = 0x25;

    /* empty PLT: create PLT0 entry that pushes the library identifier
       (GOT + PTR_SIZE) and jumps to ld.so resolution routine
       (GOT + 2 * PTR_SIZE) */
    if (plt->data_offset == 0) {
        p = section_ptr_add(plt, 16);
        p[0] = 0xff; /* pushl got + PTR_SIZE */
        p[1] = modrm + 0x10;
        write32le(p + 2, PTR_SIZE);
        p[6] = 0xff; /* jmp *(got + PTR_SIZE * 2) */
        p[7] = modrm;
        write32le(p + 8, PTR_SIZE * 2);
    }
    plt_offset = plt->data_offset;

    /* The PLT slot refers to the relocation entry it needs via offset.
       The reloc entry is created below, so its offset is the current
       data_offset */
    relofs = s1->got->reloc ? s1->got->reloc->data_offset : 0;

    /* Jump to GOT entry where ld.so initially put the address of ip + 4 */
    p = section_ptr_add(plt, 16);
    p[0] = 0xff; /* jmp *(got + x) */
    p[1] = modrm;
    write32le(p + 2, got_offset);
    p[6] = 0x68; /* push $xxx */
    write32le(p + 7, relofs);
    p[11] = 0xe9; /* jmp plt_start */
    write32le(p + 12, -(plt->data_offset));
    return plt_offset;
}

/* relocate the PLT: compute addresses and offsets in the PLT now that final
   address for PLT and GOT are known (see fill_program_header) */
ST_FUNC void relocate_plt(TCCState *s1)
{
    uint8_t *p, *p_end;

    if (!s1->plt)
      return;

    p = s1->plt->data;
    p_end = p + s1->plt->data_offset;

    if (p < p_end) {
        add32le(p + 2, s1->got->sh_addr);
        add32le(p + 8, s1->got->sh_addr);
        p += 16;
        while (p < p_end) {
            add32le(p + 2, s1->got->sh_addr);
            p += 16;
        }
    }
}

static ElfW_Rel *qrel; /* ptr to next reloc entry reused */

void relocate_init(Section *sr)
{
    qrel = (ElfW_Rel *) sr->data;
}

void relocate(TCCState *s1, ElfW_Rel *rel, int type, unsigned char *ptr, addr_t addr, addr_t val)
{
    int sym_index, esym_index;

    sym_index = ELFW(R_SYM)(rel->r_info);

    switch (type) {
        case R_386_32:
            if (s1->output_type == TCC_OUTPUT_DLL) {
                esym_index = s1->sym_attrs[sym_index].dyn_index;
                qrel->r_offset = rel->r_offset;
                if (esym_index) {
                    qrel->r_info = ELFW(R_INFO)(esym_index, R_386_32);
                    qrel++;
                    return;
                } else {
                    qrel->r_info = ELFW(R_INFO)(0, R_386_RELATIVE);
                    qrel++;
                }
            }
            add32le(ptr, val);
            return;
        case R_386_PC32:
            if (s1->output_type == TCC_OUTPUT_DLL) {
                /* DLL relocation */
                esym_index = s1->sym_attrs[sym_index].dyn_index;
                if (esym_index) {
                    qrel->r_offset = rel->r_offset;
                    qrel->r_info = ELFW(R_INFO)(esym_index, R_386_PC32);
                    qrel++;
                    return;
                }
            }
            add32le(ptr, val - addr);
            return;
        case R_386_PLT32:
            add32le(ptr, val - addr);
            return;
        case R_386_GLOB_DAT:
        case R_386_JMP_SLOT:
            write32le(ptr, val);
            return;
        case R_386_GOTPC:
            add32le(ptr, s1->got->sh_addr - addr);
            return;
        case R_386_GOTOFF:
            add32le(ptr, val - s1->got->sh_addr);
            return;
        case R_386_GOT32:
        case R_386_GOT32X:
            /* we load the got offset */
            add32le(ptr, s1->sym_attrs[sym_index].got_offset);
            return;
        case R_386_16:
            if (s1->output_format != TCC_OUTPUT_FORMAT_BINARY) {
            output_file:
                tcc_error(-1, "can only produce 16-bit binary files");
            }
            write16le(ptr, read16le(ptr) + val);
            return;
        case R_386_PC16:
            if (s1->output_format != TCC_OUTPUT_FORMAT_BINARY)
                goto output_file;
            write16le(ptr, read16le(ptr) + val - addr);
            return;
        case R_386_RELATIVE:
#ifdef TCC_TARGET_PE
            add32le(ptr, val - s1->pe_imagebase);
#endif
            /* do nothing */
            return;
        case R_386_COPY:
            /* This relocation must copy initialized data from the library
            to the program .bss segment. Currently made like for ARM
            (to remove noise of default case). Is this true?
            */
            return;
        default:
            fprintf(stderr,"FIXME: handle reloc type %d at %x [%p] to %x\n",
                type, (unsigned)addr, ptr, (unsigned)val);
            return;
    }
}

#endif  /**  #ifdef TCC_TARGET_I386  **/

#ifdef TCC_TARGET_ARM
#include "arm-gen.c"
#include "arm-link.c"
#include "arm-asm.c"
#endif
#ifdef TCC_TARGET_ARM64
#include "arm64-gen.c"
#include "arm64-link.c"
#endif
#ifdef TCC_TARGET_C67
#include "c67-gen.c"
#include "c67-link.c"
#include "tcccoff.c"
#endif
#ifdef TCC_TARGET_X86_64

/**  #include "x86_64-gen.c"  **/

/*  x86-64 code generator for TCC
 *  Copyright (c) 2008 Shinichiro Hamaji
 *  Based on i386-gen.c by Fabrice Bellard
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */

#include <assert.h>

ST_DATA const int reg_classes[NB_REGS] = {
    /* eax */ RC_INT | RC_RAX,
    /* ecx */ RC_INT | RC_RCX,
    /* edx */ RC_INT | RC_RDX,
    0,
    0,
    0,
    0,
    0,
    RC_R8,
    RC_R9,
    RC_R10,
    RC_R11,
    0,
    0,
    0,
    0,
    /* xmm0 */ RC_FLOAT | RC_XMM0,
    /* xmm1 */ RC_FLOAT | RC_XMM1,
    /* xmm2 */ RC_FLOAT | RC_XMM2,
    /* xmm3 */ RC_FLOAT | RC_XMM3,
    /* xmm4 */ RC_FLOAT | RC_XMM4,
    /* xmm5 */ RC_FLOAT | RC_XMM5,
    /* xmm6 an xmm7 are included so gv() can be used on them,
       but they are not tagged with RC_FLOAT because they are
       callee saved on Windows */
    RC_XMM6,
    RC_XMM7,
    /* st0 */ RC_ST0
};

static unsigned long func_sub_sp_offset;
static int func_ret_sub;

/* XXX: make it faster ? */
ST_FUNC void g(int c)
{
    int ind1;
    if (nocode_wanted)
        return;
    ind1 = ind + 1;
    if (ind1 > cur_text_section->data_allocated)
        section_realloc(cur_text_section, ind1);
    cur_text_section->data[ind] = c;
    ind = ind1;
}

ST_FUNC void o(unsigned int c)
{
    while (c) {
        g(c);
        c = c >> 8;
    }
}

ST_FUNC void gen_le16(int v)
{
    g(v);
    g(v >> 8);
}

ST_FUNC void gen_le32(int c)
{
    g(c);
    g(c >> 8);
    g(c >> 16);
    g(c >> 24);
}

ST_FUNC void gen_le64(int64_t c)
{
    g(c);
    g(c >> 8);
    g(c >> 16);
    g(c >> 24);
    g(c >> 32);
    g(c >> 40);
    g(c >> 48);
    g(c >> 56);
}

static void orex(int ll, int r, int r2, int b)
{
    if ((r & VT_VALMASK) >= VT_CONST)
        r = 0;
    if ((r2 & VT_VALMASK) >= VT_CONST)
        r2 = 0;
    if (ll || REX_BASE(r) || REX_BASE(r2))
        o(0x40 | REX_BASE(r) | (REX_BASE(r2) << 2) | (ll << 3));
    o(b);
}

/* output a symbol and patch all calls to it */
ST_FUNC void gsym_addr(int t, int a)
{
    while (t) {
        unsigned char *ptr = cur_text_section->data + t;
        uint32_t n = read32le(ptr); /* next value */
        write32le(ptr, a - t - 4);
        t = n;
    }
}

void gsym(int t)
{
    gsym_addr(t, ind);
}


static int is64_type(int t)
{
    return ((t & VT_BTYPE) == VT_PTR ||
            (t & VT_BTYPE) == VT_FUNC ||
            (t & VT_BTYPE) == VT_LLONG);
}

/* instruction + 4 bytes data. Return the address of the data */
static int oad(int c, int s)
{
    int t;
    if (nocode_wanted)
        return s;
    o(c);
    t = ind;
    gen_le32(s);
    return t;
}

/* generate jmp to a label */
#define gjmp2(instr,lbl) oad(instr,lbl)

ST_FUNC void gen_addr32(int r, Sym *sym, int c)
{
    if (r & VT_SYM)
        greloca(cur_text_section, sym, ind, R_X86_64_32S, c), c=0;
    gen_le32(c);
}

/* output constant with relocation if 'r & VT_SYM' is true */
ST_FUNC void gen_addr64(int r, Sym *sym, int64_t c)
{
    if (r & VT_SYM)
        greloca(cur_text_section, sym, ind, R_X86_64_64, c), c=0;
    gen_le64(c);
}

/* output constant with relocation if 'r & VT_SYM' is true */
ST_FUNC void gen_addrpc32(int r, Sym *sym, int c)
{
    if (r & VT_SYM)
        greloca(cur_text_section, sym, ind, R_X86_64_PC32, c-4), c=4;
    gen_le32(c-4);
}

/* output got address with relocation */
static void gen_gotpcrel(int r, Sym *sym, int c)
{
    greloca(cur_text_section, sym, ind, R_X86_64_GOTPCREL, -4);
    gen_le32(0);
    if (c) {
        /* we use add c, %xxx for displacement */
        orex(1, r, 0, 0x81);
        o(0xc0 + REG_VALUE(r));
        gen_le32(c);
    }
}

static void gen_modrm_impl(int op_reg, int r, Sym *sym, int c, int is_got)
{
    op_reg = REG_VALUE(op_reg) << 3;
    if ((r & VT_VALMASK) == VT_CONST) {
        /* constant memory reference */
	if (!(r & VT_SYM)) {
	    /* Absolute memory reference */
	    o(0x04 | op_reg); /* [sib] | destreg */
	    oad(0x25, c);     /* disp32 */
	} else {
	    o(0x05 | op_reg); /* (%rip)+disp32 | destreg */
	    if (is_got) {
		gen_gotpcrel(r, sym, c);
	    } else {
		gen_addrpc32(r, sym, c);
	    }
	}
    } else if ((r & VT_VALMASK) == VT_LOCAL) {
        /* currently, we use only ebp as base */
        if (c == (char)c) {
            /* short reference */
            o(0x45 | op_reg);
            g(c);
        } else {
            oad(0x85 | op_reg, c);
        }
    } else if ((r & VT_VALMASK) >= TREG_MEM) {
        if (c) {
            g(0x80 | op_reg | REG_VALUE(r));
            gen_le32(c);
        } else {
            g(0x00 | op_reg | REG_VALUE(r));
        }
    } else {
        g(0x00 | op_reg | REG_VALUE(r));
    }
}

/* generate a modrm reference. 'op_reg' contains the additional 3
   opcode bits */
static void gen_modrm(int op_reg, int r, Sym *sym, int c)
{
    gen_modrm_impl(op_reg, r, sym, c, 0);
}

/* generate a modrm reference. 'op_reg' contains the additional 3
   opcode bits */
static void gen_modrm64(int opcode, int op_reg, int r, Sym *sym, int c)
{
    int is_got;
    is_got = (op_reg & TREG_MEM) && !(sym->type.t & VT_STATIC);
    orex(1, r, op_reg, opcode);
    gen_modrm_impl(op_reg, r, sym, c, is_got);
}


/* load 'r' from value 'sv' */
void load(int r, SValue *sv)
{
    int v, t, ft, fc, fr;
    SValue v1;

#ifdef TCC_TARGET_PE
    SValue v2;
    sv = pe_getimport(sv, &v2);
#endif

    fr = sv->r;
    ft = sv->type.t & ~VT_DEFSIGN;
    fc = sv->c.i;
    if( fc != sv->c.i && ( fr & VT_SYM ))  tcc_error(-1, "64 bit addend in load");

    ft &= ~(VT_VOLATILE | VT_CONSTANT);

#ifndef TCC_TARGET_PE
    /* we use indirect access via got */
    if ((fr & VT_VALMASK) == VT_CONST && (fr & VT_SYM) &&
        (fr & VT_LVAL) && !(sv->sym->type.t & VT_STATIC)) {
        /* use the result register as a temporal register */
        int tr = r | TREG_MEM;
        if (is_float(ft)) {
            /* we cannot use float registers as a temporal register */
            tr = get_reg(RC_INT) | TREG_MEM;
        }
        gen_modrm64(0x8b, tr, fr, sv->sym, 0);

        /* load from the temporal register */
        fr = tr | VT_LVAL;
    }
#endif

    v = fr & VT_VALMASK;
    if (fr & VT_LVAL) {
        int b, ll;
        if (v == VT_LLOCAL) {
            v1.type.t = VT_PTR;
            v1.r = VT_LOCAL | VT_LVAL;
            v1.c.i = fc;
            fr = r;
            if (!(reg_classes[fr] & (RC_INT|RC_R11)))
                fr = get_reg(RC_INT);
            load(fr, &v1);
        }
	if (fc != sv->c.i) {
	    /* If the addends doesn't fit into a 32bit signed
	       we must use a 64bit move.  We've checked above
	       that this doesn't have a sym associated.  */
	    v1.type.t = VT_LLONG;
	    v1.r = VT_CONST;
	    v1.c.i = sv->c.i;
	    fr = r;
	    if (!(reg_classes[fr] & (RC_INT|RC_R11)))
	        fr = get_reg(RC_INT);
	    load(fr, &v1);
	    fc = 0;
	}
        ll = 0;
	/* Like GCC we can load from small enough properly sized
	   structs and unions as well.
	   XXX maybe move to generic operand handling, but should
	   occur only with asm, so tccasm.c might also be a better place */
	if ((ft & VT_BTYPE) == VT_STRUCT) {
	    int align;
	    switch (type_size(&sv->type, &align)) {
		case 1: ft = VT_BYTE; break;
		case 2: ft = VT_SHORT; break;
		case 4: ft = VT_INT; break;
		case 8: ft = VT_LLONG; break;
		default:
		    tcc_error(-1, "invalid aggregate type for register load");
		    break;
	    }
	}
        if ((ft & VT_BTYPE) == VT_FLOAT) {
            b = 0x6e0f66;
            r = REG_VALUE(r); /* movd */
        } else if ((ft & VT_BTYPE) == VT_DOUBLE) {
            b = 0x7e0ff3; /* movq */
            r = REG_VALUE(r);
        } else if ((ft & VT_BTYPE) == VT_LDOUBLE) {
            b = 0xdb, r = 5; /* fldt */
        } else if ((ft & VT_TYPE) == VT_BYTE || (ft & VT_TYPE) == VT_BOOL) {
            b = 0xbe0f;   /* movsbl */
        } else if ((ft & VT_TYPE) == (VT_BYTE | VT_UNSIGNED)) {
            b = 0xb60f;   /* movzbl */
        } else if ((ft & VT_TYPE) == VT_SHORT) {
            b = 0xbf0f;   /* movswl */
        } else if ((ft & VT_TYPE) == (VT_SHORT | VT_UNSIGNED)) {
            b = 0xb70f;   /* movzwl */
        } else {
            assert(((ft & VT_BTYPE) == VT_INT)
                   || ((ft & VT_BTYPE) == VT_LLONG)
                   || ((ft & VT_BTYPE) == VT_PTR)
                   || ((ft & VT_BTYPE) == VT_FUNC)
                );
            ll = is64_type(ft);
            b = 0x8b;
        }
        if (ll) {
            gen_modrm64(b, r, fr, sv->sym, fc);
        } else {
            orex(ll, fr, r, b);
            gen_modrm(r, fr, sv->sym, fc);
        }
    } else {
        if (v == VT_CONST) {
            if (fr & VT_SYM) {
#ifdef TCC_TARGET_PE
                orex(1,0,r,0x8d);
                o(0x05 + REG_VALUE(r) * 8); /* lea xx(%rip), r */
                gen_addrpc32(fr, sv->sym, fc);
#else
                if (sv->sym->type.t & VT_STATIC) {
                    orex(1,0,r,0x8d);
                    o(0x05 + REG_VALUE(r) * 8); /* lea xx(%rip), r */
                    gen_addrpc32(fr, sv->sym, fc);
                } else {
                    orex(1,0,r,0x8b);
                    o(0x05 + REG_VALUE(r) * 8); /* mov xx(%rip), r */
                    gen_gotpcrel(r, sv->sym, fc);
                }
#endif
            } else if (is64_type(ft)) {
                orex(1,r,0, 0xb8 + REG_VALUE(r)); /* mov $xx, r */
                gen_le64(sv->c.i);
            } else {
                orex(0,r,0, 0xb8 + REG_VALUE(r)); /* mov $xx, r */
                gen_le32(fc);
            }
        } else if (v == VT_LOCAL) {
            orex(1,0,r,0x8d); /* lea xxx(%ebp), r */
            gen_modrm(r, VT_LOCAL, sv->sym, fc);
        } else if (v == VT_CMP) {
            orex(0,r,0,0);
	    if ((fc & ~0x100) != TOK_NE)
              oad(0xb8 + REG_VALUE(r), 0); /* mov $0, r */
	    else
              oad(0xb8 + REG_VALUE(r), 1); /* mov $1, r */
	    if (fc & 0x100)
	      {
	        /* This was a float compare.  If the parity bit is
		   set the result was unordered, meaning false for everything
		   except TOK_NE, and true for TOK_NE.  */
		fc &= ~0x100;
		o(0x037a + (REX_BASE(r) << 8));
	      }
            orex(0,r,0, 0x0f); /* setxx %br */
            o(fc);
            o(0xc0 + REG_VALUE(r));
        } else if (v == VT_JMP || v == VT_JMPI) {
            t = v & 1;
            orex(0,r,0,0);
            oad(0xb8 + REG_VALUE(r), t); /* mov $1, r */
            o(0x05eb + (REX_BASE(r) << 8)); /* jmp after */
            gsym(fc);
            orex(0,r,0,0);
            oad(0xb8 + REG_VALUE(r), t ^ 1); /* mov $0, r */
        } else if (v != r) {
            if ((r >= TREG_XMM0) && (r <= TREG_XMM7)) {
                if (v == TREG_ST0) {
                    /* gen_cvt_ftof(VT_DOUBLE); */
                    o(0xf0245cdd); /* fstpl -0x10(%rsp) */
                    /* movsd -0x10(%rsp),%xmmN */
                    o(0x100ff2);
                    o(0x44 + REG_VALUE(r)*8); /* %xmmN */
                    o(0xf024);
                } else {
                    assert((v >= TREG_XMM0) && (v <= TREG_XMM7));
                    if ((ft & VT_BTYPE) == VT_FLOAT) {
                        o(0x100ff3);
                    } else {
                        assert((ft & VT_BTYPE) == VT_DOUBLE);
                        o(0x100ff2);
                    }
                    o(0xc0 + REG_VALUE(v) + REG_VALUE(r)*8);
                }
            } else if (r == TREG_ST0) {
                assert((v >= TREG_XMM0) && (v <= TREG_XMM7));
                /* gen_cvt_ftof(VT_LDOUBLE); */
                /* movsd %xmmN,-0x10(%rsp) */
                o(0x110ff2);
                o(0x44 + REG_VALUE(r)*8); /* %xmmN */
                o(0xf024);
                o(0xf02444dd); /* fldl -0x10(%rsp) */
            } else {
                orex(1,r,v, 0x89);
                o(0xc0 + REG_VALUE(r) + REG_VALUE(v) * 8); /* mov v, r */
            }
        }
    }
}

/* store register 'r' in lvalue 'v' */
void store(int r, SValue *v)
{
    int fr, bt, ft, fc;
    int op64 = 0;
    /* store the REX prefix in this variable when PIC is enabled */
    int pic = 0;

#ifdef TCC_TARGET_PE
    SValue v2;
    v = pe_getimport(v, &v2);
#endif

    fr = v->r & VT_VALMASK;
    ft = v->type.t;
    fc = v->c.i;
    if( fc != v->c.i && ( fr & VT_SYM ))  tcc_error(-1, "64 bit addend in store");
    ft &= ~(VT_VOLATILE | VT_CONSTANT);
    bt = ft & VT_BTYPE;

#ifndef TCC_TARGET_PE
    /* we need to access the variable via got */
    if (fr == VT_CONST && (v->r & VT_SYM)) {
        /* mov xx(%rip), %r11 */
        o(0x1d8b4c);
        gen_gotpcrel(TREG_R11, v->sym, v->c.i);
        pic = is64_type(bt) ? 0x49 : 0x41;
    }
#endif

    /* XXX: incorrect if float reg to reg */
    if (bt == VT_FLOAT) {
        o(0x66);
        o(pic);
        o(0x7e0f); /* movd */
        r = REG_VALUE(r);
    } else if (bt == VT_DOUBLE) {
        o(0x66);
        o(pic);
        o(0xd60f); /* movq */
        r = REG_VALUE(r);
    } else if (bt == VT_LDOUBLE) {
        o(0xc0d9); /* fld %st(0) */
        o(pic);
        o(0xdb); /* fstpt */
        r = 7;
    } else {
        if (bt == VT_SHORT)
            o(0x66);
        o(pic);
        if (bt == VT_BYTE || bt == VT_BOOL)
            orex(0, 0, r, 0x88);
        else if (is64_type(bt))
            op64 = 0x89;
        else
            orex(0, 0, r, 0x89);
    }
    if (pic) {
        /* xxx r, (%r11) where xxx is mov, movq, fld, or etc */
        if (op64)
            o(op64);
        o(3 + (r << 3));
    } else if (op64) {
        if (fr == VT_CONST || fr == VT_LOCAL || (v->r & VT_LVAL)) {
            gen_modrm64(op64, r, v->r, v->sym, fc);
        } else if (fr != r) {
            /* XXX: don't we really come here? */
            abort();
            o(0xc0 + fr + r * 8); /* mov r, fr */
        }
    } else {
        if (fr == VT_CONST || fr == VT_LOCAL || (v->r & VT_LVAL)) {
            gen_modrm(r, v->r, v->sym, fc);
        } else if (fr != r) {
            /* XXX: don't we really come here? */
            abort();
            o(0xc0 + fr + r * 8); /* mov r, fr */
        }
    }
}

/* 'is_jmp' is '1' if it is a jump */
static void gcall_or_jmp(int is_jmp)
{
    int r;
    if ((vtop->r & (VT_VALMASK | VT_LVAL)) == VT_CONST &&
	((vtop->r & VT_SYM) || (vtop->c.i-4) == (int)(vtop->c.i-4))) {
        /* constant case */
        if (vtop->r & VT_SYM) {
            /* relocation case */
#ifdef TCC_TARGET_PE
            greloca(cur_text_section, vtop->sym, ind + 1, R_X86_64_PC32, (int)(vtop->c.i-4));
#else
            greloca(cur_text_section, vtop->sym, ind + 1, R_X86_64_PLT32, (int)(vtop->c.i-4));
#endif
        } else {
            /* put an empty PC32 relocation */
            put_elf_reloca(symtab_section, cur_text_section,
                          ind + 1, R_X86_64_PC32, 0, (int)(vtop->c.i-4));
        }
        oad(0xe8 + is_jmp, 0); /* call/jmp im */
    } else {
        /* otherwise, indirect call */
        r = TREG_R11;
        load(r, vtop);
        o(0x41); /* REX */
        o(0xff); /* call/jmp *r */
        o(0xd0 + REG_VALUE(r) + (is_jmp << 4));
    }
}

#if defined(CONFIG_TCC_BCHECK)
#ifndef TCC_TARGET_PE
static addr_t func_bound_offset;
static unsigned long func_bound_ind;
#endif

static void gen_static_call(int v)
{
    Sym *sym = external_global_sym(v, &func_old_type, 0);
    oad(0xe8, 0);
    greloca(cur_text_section, sym, ind-4, R_X86_64_PC32, -4);
}

/* generate a bounded pointer addition */
ST_FUNC void gen_bounded_ptr_add(void)
{
    /* save all temporary registers */
    save_regs(0);

    /* prepare fast x86_64 function call */
    gv(RC_RAX);
    o(0xc68948); // mov  %rax,%rsi ## second arg in %rsi, this must be size
    vtop--;

    gv(RC_RAX);
    o(0xc78948); // mov  %rax,%rdi ## first arg in %rdi, this must be ptr
    vtop--;

    /* do a fast function call */
    gen_static_call(TOK___bound_ptr_add);

    /* returned pointer is in rax */
    vtop++;
    vtop->r = TREG_RAX | VT_BOUNDED;


    /* relocation offset of the bounding function call point */
    vtop->c.i = (cur_text_section->reloc->data_offset - sizeof(ElfW(Rela)));
}

/* patch pointer addition in vtop so that pointer dereferencing is
   also tested */
ST_FUNC void gen_bounded_ptr_deref(void)
{
    addr_t func;
    int size, align;
    ElfW(Rela) *rel;
    Sym *sym;

    size = 0;
    /* XXX: put that code in generic part of tcc */
    if (!is_float(vtop->type.t)) {
        if (vtop->r & VT_LVAL_BYTE)
            size = 1;
        else if (vtop->r & VT_LVAL_SHORT)
            size = 2;
    }
    if (!size)
    size = type_size(&vtop->type, &align);
    switch(size) {
    case  1: func = TOK___bound_ptr_indir1; break;
    case  2: func = TOK___bound_ptr_indir2; break;
    case  4: func = TOK___bound_ptr_indir4; break;
    case  8: func = TOK___bound_ptr_indir8; break;
    case 12: func = TOK___bound_ptr_indir12; break;
    case 16: func = TOK___bound_ptr_indir16; break;
    default:
        tcc_error(-1, "unhandled size when dereferencing bounded pointer");
        func = 0;
        break;
    }

    sym = external_global_sym(func, &func_old_type, 0);
    if (!sym->c)
        put_extern_sym(sym, NULL, 0, 0);

    /* patch relocation */
    /* XXX: find a better solution ? */

    rel = (ElfW(Rela) *)(cur_text_section->reloc->data + vtop->c.i);
    rel->r_info = ELF64_R_INFO(sym->c, ELF64_R_TYPE(rel->r_info));
}
#endif

#ifdef TCC_TARGET_PE

#define REGN 4
static const uint8_t arg_regs[REGN] = {
    TREG_RCX, TREG_RDX, TREG_R8, TREG_R9
};

/* Prepare arguments in R10 and R11 rather than RCX and RDX
   because gv() will not ever use these */
static int arg_prepare_reg(int idx) {
  if (idx == 0 || idx == 1)
      /* idx=0: r10, idx=1: r11 */
      return idx + 10;
  else
      return arg_regs[idx];
}

static int func_scratch, func_alloca;

/* Generate function call. The function address is pushed first, then
   all the parameters in call order. This functions pops all the
   parameters and the function address. */

static void gen_offs_sp(int b, int r, int d)
{
    orex(1,0,r & 0x100 ? 0 : r, b);
    if (d == (char)d) {
        o(0x2444 | (REG_VALUE(r) << 3));
        g(d);
    } else {
        o(0x2484 | (REG_VALUE(r) << 3));
        gen_le32(d);
    }
}

static int using_regs(int size)
{
    return !(size > 8 || (size & (size - 1)));
}

/* Return the number of registers needed to return the struct, or 0 if
   returning via struct pointer. */
ST_FUNC int gfunc_sret(CType *vt, int variadic, CType *ret, int *ret_align, int *regsize)
{
    int size, align;
    *ret_align = 1; // Never have to re-align return values for x86-64
    *regsize = 8;
    size = type_size(vt, &align);
    if (!using_regs(size))
        return 0;
    if (size == 8)
        ret->t = VT_LLONG;
    else if (size == 4)
        ret->t = VT_INT;
    else if (size == 2)
        ret->t = VT_SHORT;
    else
        ret->t = VT_BYTE;
    ret->ref = NULL;
    return 1;
}

static int is_sse_float(int t) {
    int bt;
    bt = t & VT_BTYPE;
    return bt == VT_DOUBLE || bt == VT_FLOAT;
}

static int gfunc_arg_size(CType *type) {
    int align;
    if (type->t & (VT_ARRAY|VT_BITFIELD))
        return 8;
    return type_size(type, &align);
}

void gfunc_call(int nb_args)
{
    int size, r, args_size, i, d, bt, struct_size;
    int arg;

    args_size = (nb_args < REGN ? REGN : nb_args) * PTR_SIZE;
    arg = nb_args;

    /* for struct arguments, we need to call memcpy and the function
       call breaks register passing arguments we are preparing.
       So, we process arguments which will be passed by stack first. */
    struct_size = args_size;
    for(i = 0; i < nb_args; i++) {
        SValue *sv;
        
        --arg;
        sv = &vtop[-i];
        bt = (sv->type.t & VT_BTYPE);
        size = gfunc_arg_size(&sv->type);

        if (using_regs(size))
            continue; /* arguments smaller than 8 bytes passed in registers or on stack */

        if (bt == VT_STRUCT) {
            /* align to stack align size */
            size = (size + 15) & ~15;
            /* generate structure store */
            r = get_reg(RC_INT);
            gen_offs_sp(0x8d, r, struct_size);
            struct_size += size;

            /* generate memcpy call */
            vset(&sv->type, r | VT_LVAL, 0);
            vpushv(sv);
            vstore();
            --vtop;
        } else if (bt == VT_LDOUBLE) {
            gv(RC_ST0);
            gen_offs_sp(0xdb, 0x107, struct_size);
            struct_size += 16;
        }
    }

    if (func_scratch < struct_size)
        func_scratch = struct_size;

    arg = nb_args;
    struct_size = args_size;

    for(i = 0; i < nb_args; i++) {
        --arg;
        bt = (vtop->type.t & VT_BTYPE);

        size = gfunc_arg_size(&vtop->type);
        if (!using_regs(size)) {
            /* align to stack align size */
            size = (size + 15) & ~15;
            if (arg >= REGN) {
                d = get_reg(RC_INT);
                gen_offs_sp(0x8d, d, struct_size);
                gen_offs_sp(0x89, d, arg*8);
            } else {
                d = arg_prepare_reg(arg);
                gen_offs_sp(0x8d, d, struct_size);
            }
            struct_size += size;
        } else {
            if (is_sse_float(vtop->type.t)) {
		if( tcc_state->nosse )  tcc_error(-1, "SSE disabled");
                gv(RC_XMM0); /* only use one float register */
                if (arg >= REGN) {
                    /* movq %xmm0, j*8(%rsp) */
                    gen_offs_sp(0xd60f66, 0x100, arg*8);
                } else {
                    /* movaps %xmm0, %xmmN */
                    o(0x280f);
                    o(0xc0 + (arg << 3));
                    d = arg_prepare_reg(arg);
                    /* mov %xmm0, %rxx */
                    o(0x66);
                    orex(1,d,0, 0x7e0f);
                    o(0xc0 + REG_VALUE(d));
                }
            } else {
                if (bt == VT_STRUCT) {
                    vtop->type.ref = NULL;
                    vtop->type.t = size > 4 ? VT_LLONG : size > 2 ? VT_INT
                        : size > 1 ? VT_SHORT : VT_BYTE;
                }
                
                r = gv(RC_INT);
                if (arg >= REGN) {
                    gen_offs_sp(0x89, r, arg*8);
                } else {
                    d = arg_prepare_reg(arg);
                    orex(1,d,r,0x89); /* mov */
                    o(0xc0 + REG_VALUE(r) * 8 + REG_VALUE(d));
                }
            }
        }
        vtop--;
    }
    save_regs(0);
    
    /* Copy R10 and R11 into RCX and RDX, respectively */
    if (nb_args > 0) {
        o(0xd1894c); /* mov %r10, %rcx */
        if (nb_args > 1) {
            o(0xda894c); /* mov %r11, %rdx */
        }
    }
    
    gcall_or_jmp(0);

    if ((vtop->r & VT_SYM) && vtop->sym->v == TOK_alloca) {
        /* need to add the "func_scratch" area after alloca */
        o(0x0548), gen_le32(func_alloca), func_alloca = ind - 4;
    }

    /* other compilers don't clear the upper bits when returning char/short */
    bt = vtop->type.ref->type.t & (VT_BTYPE | VT_UNSIGNED);
    if (bt == (VT_BYTE | VT_UNSIGNED))
        o(0xc0b60f);  /* movzbl %al, %eax */
    else if (bt == VT_BYTE)
        o(0xc0be0f); /* movsbl %al, %eax */
    else if (bt == VT_SHORT)
        o(0x98); /* cwtl */
    else if (bt == (VT_SHORT | VT_UNSIGNED))
        o(0xc0b70f);  /* movzbl %al, %eax */
#if 0 /* handled in gen_cast() */
    else if (bt == VT_INT)
        o(0x9848); /* cltq */
    else if (bt == (VT_INT | VT_UNSIGNED))
        o(0xc089); /* mov %eax,%eax */
#endif
    vtop--;
}


#define FUNC_PROLOG_SIZE 11

/* generate function prolog of type 't' */
void gfunc_prolog(CType *func_type)
{
    int addr, reg_param_index, bt, size;
    Sym *sym;
    CType *type;

    func_ret_sub = 0;
    func_scratch = 0;
    func_alloca = 0;
    loc = 0;

    addr = PTR_SIZE * 2;
    ind += FUNC_PROLOG_SIZE;
    func_sub_sp_offset = ind;
    reg_param_index = 0;

    sym = func_type->ref;

    /* if the function returns a structure, then add an
       implicit pointer parameter */
    func_vt = sym->type;
    func_var = (sym->f.func_type == FUNC_ELLIPSIS);
    size = gfunc_arg_size(&func_vt);
    if (!using_regs(size)) {
        gen_modrm64(0x89, arg_regs[reg_param_index], VT_LOCAL, NULL, addr);
        func_vc = addr;
        reg_param_index++;
        addr += 8;
    }

    /* define parameters */
    while ((sym = sym->next) != NULL) {
        type = &sym->type;
        bt = type->t & VT_BTYPE;
        size = gfunc_arg_size(type);
        if (!using_regs(size)) {
            if (reg_param_index < REGN) {
                gen_modrm64(0x89, arg_regs[reg_param_index], VT_LOCAL, NULL, addr);
            }
            sym_push(sym->v & ~SYM_FIELD, type, VT_LLOCAL | VT_LVAL, addr);
        } else {
            if (reg_param_index < REGN) {
                /* save arguments passed by register */
                if ((bt == VT_FLOAT) || (bt == VT_DOUBLE)) {
		    if( tcc_state->nosse )  tcc_error(-1, "SSE disabled");
                    o(0xd60f66); /* movq */
                    gen_modrm(reg_param_index, VT_LOCAL, NULL, addr);
                } else {
                    gen_modrm64(0x89, arg_regs[reg_param_index], VT_LOCAL, NULL, addr);
                }
            }
            sym_push(sym->v & ~SYM_FIELD, type, VT_LOCAL | VT_LVAL, addr);
        }
        addr += 8;
        reg_param_index++;
    }

    while (reg_param_index < REGN) {
        if (func_type->ref->f.func_type == FUNC_ELLIPSIS) {
            gen_modrm64(0x89, arg_regs[reg_param_index], VT_LOCAL, NULL, addr);
            addr += 8;
        }
        reg_param_index++;
    }
}

/* generate function epilog */
void gfunc_epilog(void)
{
    int v, saved_ind;

    o(0xc9); /* leave */
    if (func_ret_sub == 0) {
        o(0xc3); /* ret */
    } else {
        o(0xc2); /* ret n */
        g(func_ret_sub);
        g(func_ret_sub >> 8);
    }

    saved_ind = ind;
    ind = func_sub_sp_offset - FUNC_PROLOG_SIZE;
    /* align local size to word & save local variables */
    func_scratch = (func_scratch + 15) & -16;
    v = (func_scratch + -loc + 15) & -16;

    if (v >= 4096) {
        Sym *sym = external_global_sym(TOK___chkstk, &func_old_type, 0);
        oad(0xb8, v); /* mov stacksize, %eax */
        oad(0xe8, 0); /* call __chkstk, (does the stackframe too) */
        greloca(cur_text_section, sym, ind-4, R_X86_64_PC32, -4);
        o(0x90); /* fill for FUNC_PROLOG_SIZE = 11 bytes */
    } else {
        o(0xe5894855);  /* push %rbp, mov %rsp, %rbp */
        o(0xec8148);  /* sub rsp, stacksize */
        gen_le32(v);
    }

    /* add the "func_scratch" area after each alloca seen */
    while (func_alloca) {
        unsigned char *ptr = cur_text_section->data + func_alloca;
        func_alloca = read32le(ptr);
        write32le(ptr, func_scratch);
    }

    cur_text_section->data_offset = saved_ind;
    pe_add_unwind_data(ind, saved_ind, v);
    ind = cur_text_section->data_offset;
}

#else

static void gadd_sp(int val)
{
    if (val == (char)val) {
        o(0xc48348);
        g(val);
    } else {
        oad(0xc48148, val); /* add $xxx, %rsp */
    }
}

typedef enum X86_64_Mode {
  x86_64_mode_none,
  x86_64_mode_memory,
  x86_64_mode_integer,
  x86_64_mode_sse,
  x86_64_mode_x87
} X86_64_Mode;

static X86_64_Mode classify_x86_64_merge(X86_64_Mode a, X86_64_Mode b)
{
    if (a == b)
        return a;
    else if (a == x86_64_mode_none)
        return b;
    else if (b == x86_64_mode_none)
        return a;
    else if ((a == x86_64_mode_memory) || (b == x86_64_mode_memory))
        return x86_64_mode_memory;
    else if ((a == x86_64_mode_integer) || (b == x86_64_mode_integer))
        return x86_64_mode_integer;
    else if ((a == x86_64_mode_x87) || (b == x86_64_mode_x87))
        return x86_64_mode_memory;
    else
        return x86_64_mode_sse;
}

static X86_64_Mode classify_x86_64_inner(CType *ty)
{
    X86_64_Mode mode;
    Sym *f;
    
    switch (ty->t & VT_BTYPE) {
    case VT_VOID: return x86_64_mode_none;
    
    case VT_INT:
    case VT_BYTE:
    case VT_SHORT:
    case VT_LLONG:
    case VT_BOOL:
    case VT_PTR:
    case VT_FUNC:
        return x86_64_mode_integer;
    
    case VT_FLOAT:
    case VT_DOUBLE: return x86_64_mode_sse;
    
    case VT_LDOUBLE: return x86_64_mode_x87;
      
    case VT_STRUCT:
        f = ty->ref;

        mode = x86_64_mode_none;
        for (f = f->next; f; f = f->next)
            mode = classify_x86_64_merge(mode, classify_x86_64_inner(&f->type));
        
        return mode;
    }
    assert(0);
    return 0;
}

static X86_64_Mode classify_x86_64_arg(CType *ty, CType *ret, int *psize, int *palign, int *reg_count)
{
    X86_64_Mode mode;
    int size, align, ret_t = 0;
    
    if (ty->t & (VT_BITFIELD|VT_ARRAY)) {
        *psize = 8;
        *palign = 8;
        *reg_count = 1;
        ret_t = ty->t;
        mode = x86_64_mode_integer;
    } else {
        size = type_size(ty, &align);
        *psize = (size + 7) & ~7;
        *palign = (align + 7) & ~7;
    
        if (size > 16) {
            mode = x86_64_mode_memory;
        } else {
            mode = classify_x86_64_inner(ty);
            switch (mode) {
            case x86_64_mode_integer:
                if (size > 8) {
                    *reg_count = 2;
                    ret_t = VT_QLONG;
                } else {
                    *reg_count = 1;
                    ret_t = (size > 4) ? VT_LLONG : VT_INT;
                }
                break;
                
            case x86_64_mode_x87:
                *reg_count = 1;
                ret_t = VT_LDOUBLE;
                break;

            case x86_64_mode_sse:
                if (size > 8) {
                    *reg_count = 2;
                    ret_t = VT_QFLOAT;
                } else {
                    *reg_count = 1;
                    ret_t = (size > 4) ? VT_DOUBLE : VT_FLOAT;
                }
                break;
            default: break; /* nothing to be done for x86_64_mode_memory and x86_64_mode_none*/
            }
        }
    }
    
    if (ret) {
        ret->ref = NULL;
        ret->t = ret_t;
    }
    
    return mode;
}

ST_FUNC int classify_x86_64_va_arg(CType *ty)
{
    /* This definition must be synced with stdarg.h */
    enum __va_arg_type {
        __va_gen_reg, __va_float_reg, __va_stack
    };
    int size, align, reg_count;
    X86_64_Mode mode = classify_x86_64_arg(ty, NULL, &size, &align, &reg_count);
    switch (mode) {
    default: return __va_stack;
    case x86_64_mode_integer: return __va_gen_reg;
    case x86_64_mode_sse: return __va_float_reg;
    }
}

/* Return the number of registers needed to return the struct, or 0 if
   returning via struct pointer. */
ST_FUNC int gfunc_sret(CType *vt, int variadic, CType *ret, int *ret_align, int *regsize)
{
    int size, align, reg_count;
    *ret_align = 1; // Never have to re-align return values for x86-64
    *regsize = 8;
    return (classify_x86_64_arg(vt, ret, &size, &align, &reg_count) != x86_64_mode_memory);
}

#define REGN 6
static const uint8_t arg_regs[REGN] = {
    TREG_RDI, TREG_RSI, TREG_RDX, TREG_RCX, TREG_R8, TREG_R9
};

static int arg_prepare_reg(int idx) {
  if (idx == 2 || idx == 3)
      /* idx=2: r10, idx=3: r11 */
      return idx + 8;
  else
      return arg_regs[idx];
}

/* Generate function call. The function address is pushed first, then
   all the parameters in call order. This functions pops all the
   parameters and the function address. */
void gfunc_call(int nb_args)
{
    X86_64_Mode mode;
    CType type;
    int size, align, r, args_size, stack_adjust, i, reg_count;
    int nb_reg_args = 0;
    int nb_sse_args = 0;
    int sse_reg, gen_reg;
    char _onstack[nb_args], *onstack = _onstack;

    /* calculate the number of integer/float register arguments, remember
       arguments to be passed via stack (in onstack[]), and also remember
       if we have to align the stack pointer to 16 (onstack[i] == 2).  Needs
       to be done in a left-to-right pass over arguments.  */
    stack_adjust = 0;
    for(i = nb_args - 1; i >= 0; i--) {
        mode = classify_x86_64_arg(&vtop[-i].type, NULL, &size, &align, &reg_count);
        if (mode == x86_64_mode_sse && nb_sse_args + reg_count <= 8) {
            nb_sse_args += reg_count;
	    onstack[i] = 0;
	} else if (mode == x86_64_mode_integer && nb_reg_args + reg_count <= REGN) {
            nb_reg_args += reg_count;
	    onstack[i] = 0;
	} else if (mode == x86_64_mode_none) {
	    onstack[i] = 0;
	} else {
	    if (align == 16 && (stack_adjust &= 15)) {
		onstack[i] = 2;
		stack_adjust = 0;
	    } else
	      onstack[i] = 1;
	    stack_adjust += size;
	}
    }

    if( nb_sse_args && tcc_state->nosse )  tcc_error(-1, "SSE disabled but floating point arguments passed");

    /* fetch cpu flag before generating any code */
    if (vtop >= vstack && (vtop->r & VT_VALMASK) == VT_CMP)
      gv(RC_INT);

    /* for struct arguments, we need to call memcpy and the function
       call breaks register passing arguments we are preparing.
       So, we process arguments which will be passed by stack first. */
    gen_reg = nb_reg_args;
    sse_reg = nb_sse_args;
    args_size = 0;
    stack_adjust &= 15;
    for (i = 0; i < nb_args;) {
	mode = classify_x86_64_arg(&vtop[-i].type, NULL, &size, &align, &reg_count);
	if (!onstack[i]) {
	    ++i;
	    continue;
	}
        /* Possibly adjust stack to align SSE boundary.  We're processing
	   args from right to left while allocating happens left to right
	   (stack grows down), so the adjustment needs to happen _after_
	   an argument that requires it.  */
        if (stack_adjust) {
	    o(0x50); /* push %rax; aka sub $8,%rsp */
            args_size += 8;
	    stack_adjust = 0;
        }
	if (onstack[i] == 2)
	  stack_adjust = 1;

	vrotb(i+1);

	switch (vtop->type.t & VT_BTYPE) {
	    case VT_STRUCT:
		/* allocate the necessary size on stack */
		o(0x48);
		oad(0xec81, size); /* sub $xxx, %rsp */
		/* generate structure store */
		r = get_reg(RC_INT);
		orex(1, r, 0, 0x89); /* mov %rsp, r */
		o(0xe0 + REG_VALUE(r));
		vset(&vtop->type, r | VT_LVAL, 0);
		vswap();
		vstore();
		break;

	    case VT_LDOUBLE:
                gv(RC_ST0);
                oad(0xec8148, size); /* sub $xxx, %rsp */
                o(0x7cdb); /* fstpt 0(%rsp) */
                g(0x24);
                g(0x00);
		break;

	    case VT_FLOAT:
	    case VT_DOUBLE:
		assert(mode == x86_64_mode_sse);
		r = gv(RC_FLOAT);
		o(0x50); /* push $rax */
		/* movq %xmmN, (%rsp) */
		o(0xd60f66);
		o(0x04 + REG_VALUE(r)*8);
		o(0x24);
		break;

	    default:
		assert(mode == x86_64_mode_integer);
		/* simple type */
		/* XXX: implicit cast ? */
		r = gv(RC_INT);
		orex(0,r,0,0x50 + REG_VALUE(r)); /* push r */
		break;
	}
	args_size += size;

	vpop();
	--nb_args;
	onstack++;
    }

    /* XXX This should be superfluous.  */
    save_regs(0); /* save used temporary registers */

    /* then, we prepare register passing arguments.
       Note that we cannot set RDX and RCX in this loop because gv()
       may break these temporary registers. Let's use R10 and R11
       instead of them */
    assert(gen_reg <= REGN);
    assert(sse_reg <= 8);
    for(i = 0; i < nb_args; i++) {
        mode = classify_x86_64_arg(&vtop->type, &type, &size, &align, &reg_count);
        /* Alter stack entry type so that gv() knows how to treat it */
        vtop->type = type;
        if (mode == x86_64_mode_sse) {
            if (reg_count == 2) {
                sse_reg -= 2;
                gv(RC_FRET); /* Use pair load into xmm0 & xmm1 */
                if (sse_reg) { /* avoid redundant movaps %xmm0, %xmm0 */
                    /* movaps %xmm0, %xmmN */
                    o(0x280f);
                    o(0xc0 + (sse_reg << 3));
                    /* movaps %xmm1, %xmmN */
                    o(0x280f);
                    o(0xc1 + ((sse_reg+1) << 3));
                }
            } else {
                assert(reg_count == 1);
                --sse_reg;
                /* Load directly to register */
                gv(RC_XMM0 << sse_reg);
            }
        } else if (mode == x86_64_mode_integer) {
            /* simple type */
            /* XXX: implicit cast ? */
            int d;
            gen_reg -= reg_count;
            r = gv(RC_INT);
            d = arg_prepare_reg(gen_reg);
            orex(1,d,r,0x89); /* mov */
            o(0xc0 + REG_VALUE(r) * 8 + REG_VALUE(d));
            if (reg_count == 2) {
                d = arg_prepare_reg(gen_reg+1);
                orex(1,d,vtop->r2,0x89); /* mov */
                o(0xc0 + REG_VALUE(vtop->r2) * 8 + REG_VALUE(d));
            }
        }
        vtop--;
    }
    assert(gen_reg == 0);
    assert(sse_reg == 0);

    /* We shouldn't have many operands on the stack anymore, but the
       call address itself is still there, and it might be in %eax
       (or edx/ecx) currently, which the below writes would clobber.
       So evict all remaining operands here.  */
    save_regs(0);

    /* Copy R10 and R11 into RDX and RCX, respectively */
    if (nb_reg_args > 2) {
        o(0xd2894c); /* mov %r10, %rdx */
        if (nb_reg_args > 3) {
            o(0xd9894c); /* mov %r11, %rcx */
        }
    }

    if (vtop->type.ref->f.func_type != FUNC_NEW) /* implies FUNC_OLD or FUNC_ELLIPSIS */
        oad(0xb8, nb_sse_args < 8 ? nb_sse_args : 8); /* mov nb_sse_args, %eax */
    gcall_or_jmp(0);
    if (args_size)
        gadd_sp(args_size);
    vtop--;
}


#define FUNC_PROLOG_SIZE 11

static void push_arg_reg(int i) {
    loc -= 8;
    gen_modrm64(0x89, arg_regs[i], VT_LOCAL, NULL, loc);
}

/* generate function prolog of type 't' */
void gfunc_prolog(CType *func_type)
{
    X86_64_Mode mode;
    int i, addr, align, size, reg_count;
    int param_addr = 0, reg_param_index, sse_param_index;
    Sym *sym;
    CType *type;

    sym = func_type->ref;
    addr = PTR_SIZE * 2;
    loc = 0;
    ind += FUNC_PROLOG_SIZE;
    func_sub_sp_offset = ind;
    func_ret_sub = 0;

    if (sym->f.func_type == FUNC_ELLIPSIS) {
        int seen_reg_num, seen_sse_num, seen_stack_size;
        seen_reg_num = seen_sse_num = 0;
        /* frame pointer and return address */
        seen_stack_size = PTR_SIZE * 2;
        /* count the number of seen parameters */
        sym = func_type->ref;
        while ((sym = sym->next) != NULL) {
            type = &sym->type;
            mode = classify_x86_64_arg(type, NULL, &size, &align, &reg_count);
            switch (mode) {
            default:
            stack_arg:
                seen_stack_size = ((seen_stack_size + align - 1) & -align) + size;
                break;
                
            case x86_64_mode_integer:
                if (seen_reg_num + reg_count > REGN)
		    goto stack_arg;
		seen_reg_num += reg_count;
                break;
                
            case x86_64_mode_sse:
                if (seen_sse_num + reg_count > 8)
		    goto stack_arg;
		seen_sse_num += reg_count;
                break;
            }
        }

        loc -= 16;
        /* movl $0x????????, -0x10(%rbp) */
        o(0xf045c7);
        gen_le32(seen_reg_num * 8);
        /* movl $0x????????, -0xc(%rbp) */
        o(0xf445c7);
        gen_le32(seen_sse_num * 16 + 48);
        /* movl $0x????????, -0x8(%rbp) */
        o(0xf845c7);
        gen_le32(seen_stack_size);

        /* save all register passing arguments */
        for (i = 0; i < 8; i++) {
            loc -= 16;
	    if (!tcc_state->nosse) {
		o(0xd60f66); /* movq */
		gen_modrm(7 - i, VT_LOCAL, NULL, loc);
	    }
            /* movq $0, loc+8(%rbp) */
            o(0x85c748);
            gen_le32(loc + 8);
            gen_le32(0);
        }
        for (i = 0; i < REGN; i++) {
            push_arg_reg(REGN-1-i);
        }
    }

    sym = func_type->ref;
    reg_param_index = 0;
    sse_param_index = 0;

    /* if the function returns a structure, then add an
       implicit pointer parameter */
    func_vt = sym->type;
    mode = classify_x86_64_arg(&func_vt, NULL, &size, &align, &reg_count);
    if (mode == x86_64_mode_memory) {
        push_arg_reg(reg_param_index);
        func_vc = loc;
        reg_param_index++;
    }
    /* define parameters */
    while ((sym = sym->next) != NULL) {
        type = &sym->type;
        mode = classify_x86_64_arg(type, NULL, &size, &align, &reg_count);
        switch (mode) {
        case x86_64_mode_sse:
	    if( tcc_state->nosse )  tcc_error(-1, "SSE disabled but floating point arguments used");
            if (sse_param_index + reg_count <= 8) {
                /* save arguments passed by register */
                loc -= reg_count * 8;
                param_addr = loc;
                for (i = 0; i < reg_count; ++i) {
                    o(0xd60f66); /* movq */
                    gen_modrm(sse_param_index, VT_LOCAL, NULL, param_addr + i*8);
                    ++sse_param_index;
                }
            } else {
                addr = (addr + align - 1) & -align;
                param_addr = addr;
                addr += size;
            }
            break;
            
        case x86_64_mode_memory:
        case x86_64_mode_x87:
            addr = (addr + align - 1) & -align;
            param_addr = addr;
            addr += size;
            break;
            
        case x86_64_mode_integer: {
            if (reg_param_index + reg_count <= REGN) {
                /* save arguments passed by register */
                loc -= reg_count * 8;
                param_addr = loc;
                for (i = 0; i < reg_count; ++i) {
                    gen_modrm64(0x89, arg_regs[reg_param_index], VT_LOCAL, NULL, param_addr + i*8);
                    ++reg_param_index;
                }
            } else {
                addr = (addr + align - 1) & -align;
                param_addr = addr;
                addr += size;
            }
            break;
        }
	default: break; /* nothing to be done for x86_64_mode_none */
        }
        sym_push(sym->v & ~SYM_FIELD, type,
                 VT_LOCAL | VT_LVAL, param_addr);
    }

#ifdef CONFIG_TCC_BCHECK
    /* leave some room for bound checking code */
    if (tcc_state->do_bounds_check) {
        func_bound_offset = lbounds_section->data_offset;
        func_bound_ind = ind;
        oad(0xb8, 0); /* lbound section pointer */
	o(0xc78948);  /* mov  %rax,%rdi ## first arg in %rdi, this must be ptr */
	oad(0xb8, 0); /* call to function */
    }
#endif
}

/* generate function epilog */
void gfunc_epilog(void)
{
    int v, saved_ind;

#ifdef CONFIG_TCC_BCHECK
    if (tcc_state->do_bounds_check
	&& func_bound_offset != lbounds_section->data_offset)
    {
        addr_t saved_ind;
        addr_t *bounds_ptr;
        Sym *sym_data;

        /* add end of table info */
        bounds_ptr = section_ptr_add(lbounds_section, sizeof(addr_t));
        *bounds_ptr = 0;

        /* generate bound local allocation */
        sym_data = get_sym_ref(&char_pointer_type, lbounds_section, 
                               func_bound_offset, lbounds_section->data_offset);
        saved_ind = ind;
        ind = func_bound_ind;
        greloca(cur_text_section, sym_data, ind + 1, R_X86_64_64, 0);
        ind = ind + 5 + 3;
        gen_static_call(TOK___bound_local_new);
        ind = saved_ind;

        /* generate bound check local freeing */
        o(0x5250); /* save returned value, if any */
        greloca(cur_text_section, sym_data, ind + 1, R_X86_64_64, 0);
        oad(0xb8, 0); /* mov xxx, %rax */
        o(0xc78948);  /* mov %rax,%rdi # first arg in %rdi, this must be ptr */
        gen_static_call(TOK___bound_local_delete);
        o(0x585a); /* restore returned value, if any */
    }
#endif
    o(0xc9); /* leave */
    if (func_ret_sub == 0) {
        o(0xc3); /* ret */
    } else {
        o(0xc2); /* ret n */
        g(func_ret_sub);
        g(func_ret_sub >> 8);
    }
    /* align local size to word & save local variables */
    v = (-loc + 15) & -16;
    saved_ind = ind;
    ind = func_sub_sp_offset - FUNC_PROLOG_SIZE;
    o(0xe5894855);  /* push %rbp, mov %rsp, %rbp */
    o(0xec8148);  /* sub rsp, stacksize */
    gen_le32(v);
    ind = saved_ind;
}

#endif /* not PE */

/* generate a jump to a label */
int gjmp(int t)
{
    return gjmp2(0xe9, t);
}

/* generate a jump to a fixed address */
void gjmp_addr(int a)
{
    int r;
    r = a - ind - 2;
    if (r == (char)r) {
        g(0xeb);
        g(r);
    } else {
        oad(0xe9, a - ind - 5);
    }
}

ST_FUNC void gtst_addr(int inv, int a)
{
    int v = vtop->r & VT_VALMASK;
    if (v == VT_CMP) {
	inv ^= (vtop--)->c.i;
	a -= ind + 2;
	if (a == (char)a) {
	    g(inv - 32);
	    g(a);
	} else {
	    g(0x0f);
	    oad(inv - 16, a - 4);
	}
    } else if ((v & ~1) == VT_JMP) {
	if ((v & 1) != inv) {
	    gjmp_addr(a);
	    gsym(vtop->c.i);
	} else {
	    gsym(vtop->c.i);
	    o(0x05eb);
	    gjmp_addr(a);
	}
	vtop--;
    }
}

/* generate a test. set 'inv' to invert test. Stack entry is popped */
ST_FUNC int gtst(int inv, int t)
{
    int v = vtop->r & VT_VALMASK;

    if (nocode_wanted) {
        ;
    } else if (v == VT_CMP) {
        /* fast case : can jump directly since flags are set */
	if (vtop->c.i & 0x100)
	  {
	    /* This was a float compare.  If the parity flag is set
	       the result was unordered.  For anything except != this
	       means false and we don't jump (anding both conditions).
	       For != this means true (oring both).
	       Take care about inverting the test.  We need to jump
	       to our target if the result was unordered and test wasn't NE,
	       otherwise if unordered we don't want to jump.  */
	    vtop->c.i &= ~0x100;
            if (inv == (vtop->c.i == TOK_NE))
	      o(0x067a);  /* jp +6 */
	    else
	      {
	        g(0x0f);
		t = gjmp2(0x8a, t); /* jp t */
	      }
	  }
        g(0x0f);
        t = gjmp2((vtop->c.i - 16) ^ inv, t);
    } else if (v == VT_JMP || v == VT_JMPI) {
        /* && or || optimization */
        if ((v & 1) == inv) {
            /* insert vtop->c jump list in t */
            uint32_t n1, n = vtop->c.i;
            if (n) {
                while ((n1 = read32le(cur_text_section->data + n)))
                    n = n1;
                write32le(cur_text_section->data + n, t);
                t = vtop->c.i;
            }
        } else {
            t = gjmp(t);
            gsym(vtop->c.i);
        }
    }
    vtop--;
    return t;
}

/* generate an integer binary operation */
void gen_opi(int op)
{
    int r, fr, opc, c;
    int ll, uu, cc;

    ll = is64_type(vtop[-1].type.t);
    uu = (vtop[-1].type.t & VT_UNSIGNED) != 0;
    cc = (vtop->r & (VT_VALMASK | VT_LVAL | VT_SYM)) == VT_CONST;

    switch(op) {
    case '+':
    case TOK_ADDC1: /* add with carry generation */
        opc = 0;
    gen_op8:
        if (cc && (!ll || (int)vtop->c.i == vtop->c.i)) {
            /* constant case */
            vswap();
            r = gv(RC_INT);
            vswap();
            c = vtop->c.i;
            if (c == (char)c) {
                /* XXX: generate inc and dec for smaller code ? */
                orex(ll, r, 0, 0x83);
                o(0xc0 | (opc << 3) | REG_VALUE(r));
                g(c);
            } else {
                orex(ll, r, 0, 0x81);
                oad(0xc0 | (opc << 3) | REG_VALUE(r), c);
            }
        } else {
            gv2(RC_INT, RC_INT);
            r = vtop[-1].r;
            fr = vtop[0].r;
            orex(ll, r, fr, (opc << 3) | 0x01);
            o(0xc0 + REG_VALUE(r) + REG_VALUE(fr) * 8);
        }
        vtop--;
        if (op >= TOK_ULT && op <= TOK_GT) {
            vtop->r = VT_CMP;
            vtop->c.i = op;
        }
        break;
    case '-':
    case TOK_SUBC1: /* sub with carry generation */
        opc = 5;
        goto gen_op8;
    case TOK_ADDC2: /* add with carry use */
        opc = 2;
        goto gen_op8;
    case TOK_SUBC2: /* sub with carry use */
        opc = 3;
        goto gen_op8;
    case '&':
        opc = 4;
        goto gen_op8;
    case '^':
        opc = 6;
        goto gen_op8;
    case '|':
        opc = 1;
        goto gen_op8;
    case '*':
        gv2(RC_INT, RC_INT);
        r = vtop[-1].r;
        fr = vtop[0].r;
        orex(ll, fr, r, 0xaf0f); /* imul fr, r */
        o(0xc0 + REG_VALUE(fr) + REG_VALUE(r) * 8);
        vtop--;
        break;
    case TOK_SHL:
        opc = 4;
        goto gen_shift;
    case TOK_SHR:
        opc = 5;
        goto gen_shift;
    case TOK_SAR:
        opc = 7;
    gen_shift:
        opc = 0xc0 | (opc << 3);
        if (cc) {
            /* constant case */
            vswap();
            r = gv(RC_INT);
            vswap();
            orex(ll, r, 0, 0xc1); /* shl/shr/sar $xxx, r */
            o(opc | REG_VALUE(r));
            g(vtop->c.i & (ll ? 63 : 31));
        } else {
            /* we generate the shift in ecx */
            gv2(RC_INT, RC_RCX);
            r = vtop[-1].r;
            orex(ll, r, 0, 0xd3); /* shl/shr/sar %cl, r */
            o(opc | REG_VALUE(r));
        }
        vtop--;
        break;
    case TOK_UDIV:
    case TOK_UMOD:
        uu = 1;
        goto divmod;
    case '/':
    case '%':
    case TOK_PDIV:
        uu = 0;
    divmod:
        /* first operand must be in eax */
        /* XXX: need better constraint for second operand */
        gv2(RC_RAX, RC_RCX);
        r = vtop[-1].r;
        fr = vtop[0].r;
        vtop--;
        save_reg(TREG_RDX);
        orex(ll, 0, 0, uu ? 0xd231 : 0x99); /* xor %edx,%edx : cqto */
        orex(ll, fr, 0, 0xf7); /* div fr, %eax */
        o((uu ? 0xf0 : 0xf8) + REG_VALUE(fr));
        if (op == '%' || op == TOK_UMOD)
            r = TREG_RDX;
        else
            r = TREG_RAX;
        vtop->r = r;
        break;
    default:
        opc = 7;
        goto gen_op8;
    }
}

void gen_opl(int op)
{
    gen_opi(op);
}

/* generate a floating point operation 'v = t1 op t2' instruction. The
   two operands are guaranteed to have the same floating point type */
/* XXX: need to use ST1 too */
void gen_opf(int op)
{
    int a, ft, fc, swapped, r;
    int float_type =
        (vtop->type.t & VT_BTYPE) == VT_LDOUBLE ? RC_ST0 : RC_FLOAT;

    /* convert constants to memory references */
    if ((vtop[-1].r & (VT_VALMASK | VT_LVAL)) == VT_CONST) {
        vswap();
        gv(float_type);
        vswap();
    }
    if ((vtop[0].r & (VT_VALMASK | VT_LVAL)) == VT_CONST)
        gv(float_type);

    /* must put at least one value in the floating point register */
    if ((vtop[-1].r & VT_LVAL) &&
        (vtop[0].r & VT_LVAL)) {
        vswap();
        gv(float_type);
        vswap();
    }
    swapped = 0;
    /* swap the stack if needed so that t1 is the register and t2 is
       the memory reference */
    if (vtop[-1].r & VT_LVAL) {
        vswap();
        swapped = 1;
    }
    if ((vtop->type.t & VT_BTYPE) == VT_LDOUBLE) {
        if (op >= TOK_ULT && op <= TOK_GT) {
            /* load on stack second operand */
            load(TREG_ST0, vtop);
            save_reg(TREG_RAX); /* eax is used by FP comparison code */
            if (op == TOK_GE || op == TOK_GT)
                swapped = !swapped;
            else if (op == TOK_EQ || op == TOK_NE)
                swapped = 0;
            if (swapped)
                o(0xc9d9); /* fxch %st(1) */
            if (op == TOK_EQ || op == TOK_NE)
                o(0xe9da); /* fucompp */
            else
                o(0xd9de); /* fcompp */
            o(0xe0df); /* fnstsw %ax */
            if (op == TOK_EQ) {
                o(0x45e480); /* and $0x45, %ah */
                o(0x40fC80); /* cmp $0x40, %ah */
            } else if (op == TOK_NE) {
                o(0x45e480); /* and $0x45, %ah */
                o(0x40f480); /* xor $0x40, %ah */
                op = TOK_NE;
            } else if (op == TOK_GE || op == TOK_LE) {
                o(0x05c4f6); /* test $0x05, %ah */
                op = TOK_EQ;
            } else {
                o(0x45c4f6); /* test $0x45, %ah */
                op = TOK_EQ;
            }
            vtop--;
            vtop->r = VT_CMP;
            vtop->c.i = op;
        } else {
            /* no memory reference possible for long double operations */
            load(TREG_ST0, vtop);
            swapped = !swapped;

            switch(op) {
            default:
            case '+':
                a = 0;
                break;
            case '-':
                a = 4;
                if (swapped)
                    a++;
                break;
            case '*':
                a = 1;
                break;
            case '/':
                a = 6;
                if (swapped)
                    a++;
                break;
            }
            ft = vtop->type.t;
            fc = vtop->c.i;
            o(0xde); /* fxxxp %st, %st(1) */
            o(0xc1 + (a << 3));
            vtop--;
        }
    } else {
        if (op >= TOK_ULT && op <= TOK_GT) {
            /* if saved lvalue, then we must reload it */
            r = vtop->r;
            fc = vtop->c.i;
            if ((r & VT_VALMASK) == VT_LLOCAL) {
                SValue v1;
                r = get_reg(RC_INT);
                v1.type.t = VT_PTR;
                v1.r = VT_LOCAL | VT_LVAL;
                v1.c.i = fc;
                load(r, &v1);
                fc = 0;
            }

            if (op == TOK_EQ || op == TOK_NE) {
                swapped = 0;
            } else {
                if (op == TOK_LE || op == TOK_LT)
                    swapped = !swapped;
                if (op == TOK_LE || op == TOK_GE) {
                    op = 0x93; /* setae */
                } else {
                    op = 0x97; /* seta */
                }
            }

            if (swapped) {
                gv(RC_FLOAT);
                vswap();
            }
            assert(!(vtop[-1].r & VT_LVAL));
            
            if ((vtop->type.t & VT_BTYPE) == VT_DOUBLE)
                o(0x66);
            if (op == TOK_EQ || op == TOK_NE)
                o(0x2e0f); /* ucomisd */
            else
                o(0x2f0f); /* comisd */

            if (vtop->r & VT_LVAL) {
                gen_modrm(vtop[-1].r, r, vtop->sym, fc);
            } else {
                o(0xc0 + REG_VALUE(vtop[0].r) + REG_VALUE(vtop[-1].r)*8);
            }

            vtop--;
            vtop->r = VT_CMP;
            vtop->c.i = op | 0x100;
        } else {
            assert((vtop->type.t & VT_BTYPE) != VT_LDOUBLE);
            switch(op) {
            default:
            case '+':
                a = 0;
                break;
            case '-':
                a = 4;
                break;
            case '*':
                a = 1;
                break;
            case '/':
                a = 6;
                break;
            }
            ft = vtop->type.t;
            fc = vtop->c.i;
            assert((ft & VT_BTYPE) != VT_LDOUBLE);
            
            r = vtop->r;
            /* if saved lvalue, then we must reload it */
            if ((vtop->r & VT_VALMASK) == VT_LLOCAL) {
                SValue v1;
                r = get_reg(RC_INT);
                v1.type.t = VT_PTR;
                v1.r = VT_LOCAL | VT_LVAL;
                v1.c.i = fc;
                load(r, &v1);
                fc = 0;
            }
            
            assert(!(vtop[-1].r & VT_LVAL));
            if (swapped) {
                assert(vtop->r & VT_LVAL);
                gv(RC_FLOAT);
                vswap();
            }
            
            if ((ft & VT_BTYPE) == VT_DOUBLE) {
                o(0xf2);
            } else {
                o(0xf3);
            }
            o(0x0f);
            o(0x58 + a);
            
            if (vtop->r & VT_LVAL) {
                gen_modrm(vtop[-1].r, r, vtop->sym, fc);
            } else {
                o(0xc0 + REG_VALUE(vtop[0].r) + REG_VALUE(vtop[-1].r)*8);
            }

            vtop--;
        }
    }
}

/* convert integers to fp 't' type. Must handle 'int', 'unsigned int'
   and 'long long' cases. */
void gen_cvt_itof(int t)
{
    if ((t & VT_BTYPE) == VT_LDOUBLE) {
        save_reg(TREG_ST0);
        gv(RC_INT);
        if ((vtop->type.t & VT_BTYPE) == VT_LLONG) {
            /* signed long long to float/double/long double (unsigned case
               is handled generically) */
            o(0x50 + (vtop->r & VT_VALMASK)); /* push r */
            o(0x242cdf); /* fildll (%rsp) */
            o(0x08c48348); /* add $8, %rsp */
        } else if ((vtop->type.t & (VT_BTYPE | VT_UNSIGNED)) ==
                   (VT_INT | VT_UNSIGNED)) {
            /* unsigned int to float/double/long double */
            o(0x6a); /* push $0 */
            g(0x00);
            o(0x50 + (vtop->r & VT_VALMASK)); /* push r */
            o(0x242cdf); /* fildll (%rsp) */
            o(0x10c48348); /* add $16, %rsp */
        } else {
            /* int to float/double/long double */
            o(0x50 + (vtop->r & VT_VALMASK)); /* push r */
            o(0x2404db); /* fildl (%rsp) */
            o(0x08c48348); /* add $8, %rsp */
        }
        vtop->r = TREG_ST0;
    } else {
        int r = get_reg(RC_FLOAT);
        gv(RC_INT);
        o(0xf2 + ((t & VT_BTYPE) == VT_FLOAT?1:0));
        if ((vtop->type.t & (VT_BTYPE | VT_UNSIGNED)) ==
            (VT_INT | VT_UNSIGNED) ||
            (vtop->type.t & VT_BTYPE) == VT_LLONG) {
            o(0x48); /* REX */
        }
        o(0x2a0f);
        o(0xc0 + (vtop->r & VT_VALMASK) + REG_VALUE(r)*8); /* cvtsi2sd */
        vtop->r = r;
    }
}

/* convert from one floating point type to another */
void gen_cvt_ftof(int t)
{
    int ft, bt, tbt;

    ft = vtop->type.t;
    bt = ft & VT_BTYPE;
    tbt = t & VT_BTYPE;
    
    if (bt == VT_FLOAT) {
        gv(RC_FLOAT);
        if (tbt == VT_DOUBLE) {
            o(0x140f); /* unpcklps */
            o(0xc0 + REG_VALUE(vtop->r)*9);
            o(0x5a0f); /* cvtps2pd */
            o(0xc0 + REG_VALUE(vtop->r)*9);
        } else if (tbt == VT_LDOUBLE) {
            save_reg(RC_ST0);
            /* movss %xmm0,-0x10(%rsp) */
            o(0x110ff3);
            o(0x44 + REG_VALUE(vtop->r)*8);
            o(0xf024);
            o(0xf02444d9); /* flds -0x10(%rsp) */
            vtop->r = TREG_ST0;
        }
    } else if (bt == VT_DOUBLE) {
        gv(RC_FLOAT);
        if (tbt == VT_FLOAT) {
            o(0x140f66); /* unpcklpd */
            o(0xc0 + REG_VALUE(vtop->r)*9);
            o(0x5a0f66); /* cvtpd2ps */
            o(0xc0 + REG_VALUE(vtop->r)*9);
        } else if (tbt == VT_LDOUBLE) {
            save_reg(RC_ST0);
            /* movsd %xmm0,-0x10(%rsp) */
            o(0x110ff2);
            o(0x44 + REG_VALUE(vtop->r)*8);
            o(0xf024);
            o(0xf02444dd); /* fldl -0x10(%rsp) */
            vtop->r = TREG_ST0;
        }
    } else {
        int r;
        gv(RC_ST0);
        r = get_reg(RC_FLOAT);
        if (tbt == VT_DOUBLE) {
            o(0xf0245cdd); /* fstpl -0x10(%rsp) */
            /* movsd -0x10(%rsp),%xmm0 */
            o(0x100ff2);
            o(0x44 + REG_VALUE(r)*8);
            o(0xf024);
            vtop->r = r;
        } else if (tbt == VT_FLOAT) {
            o(0xf0245cd9); /* fstps -0x10(%rsp) */
            /* movss -0x10(%rsp),%xmm0 */
            o(0x100ff3);
            o(0x44 + REG_VALUE(r)*8);
            o(0xf024);
            vtop->r = r;
        }
    }
}

/* convert fp to int 't' type */
void gen_cvt_ftoi(int t)
{
    int ft, bt, size, r;
    ft = vtop->type.t;
    bt = ft & VT_BTYPE;
    if (bt == VT_LDOUBLE) {
        gen_cvt_ftof(VT_DOUBLE);
        bt = VT_DOUBLE;
    }

    gv(RC_FLOAT);
    if (t != VT_INT)
        size = 8;
    else
        size = 4;

    r = get_reg(RC_INT);
    if (bt == VT_FLOAT) {
        o(0xf3);
    } else if (bt == VT_DOUBLE) {
        o(0xf2);
    } else {
        assert(0);
    }
    orex(size == 8, r, 0, 0x2c0f); /* cvttss2si or cvttsd2si */
    o(0xc0 + REG_VALUE(vtop->r) + REG_VALUE(r)*8);
    vtop->r = r;
}

/* computed goto support */
void ggoto(void)
{
    gcall_or_jmp(1);
    vtop--;
}

/* Save the stack pointer onto the stack and return the location of its address */
ST_FUNC void gen_vla_sp_save(int addr) {
    /* mov %rsp,addr(%rbp)*/
    gen_modrm64(0x89, TREG_RSP, VT_LOCAL, NULL, addr);
}

/* Restore the SP from a location on the stack */
ST_FUNC void gen_vla_sp_restore(int addr) {
    gen_modrm64(0x8b, TREG_RSP, VT_LOCAL, NULL, addr);
}

#ifdef TCC_TARGET_PE
/* Save result of gen_vla_alloc onto the stack */
ST_FUNC void gen_vla_result(int addr) {
    /* mov %rax,addr(%rbp)*/
    gen_modrm64(0x89, TREG_RAX, VT_LOCAL, NULL, addr);
}
#endif

/* Subtract from the stack pointer, and push the resulting value onto the stack */
ST_FUNC void gen_vla_alloc(CType *type, int align) {
#ifdef TCC_TARGET_PE
    /* alloca does more than just adjust %rsp on Windows */
    vpush_global_sym(&func_old_type, TOK_alloca);
    vswap(); /* Move alloca ref past allocation size */
    gfunc_call(1);
#else
    int r;
    r = gv(RC_INT); /* allocation size */
    /* sub r,%rsp */
    o(0x2b48);
    o(0xe0 | REG_VALUE(r));
    /* We align to 16 bytes rather than align */
    /* and ~15, %rsp */
    o(0xf0e48348);
    vpop();
#endif
}


/* end of x86-64 code generator */

/*************************************************************/

/**  #include "x86_64-link.c"  **/

/* Returns 1 for a code relocation, 0 for a data relocation. For unknown
   relocations, returns -1. */
int code_reloc (int reloc_type)
{
    switch (reloc_type) {
        case R_X86_64_32:
        case R_X86_64_32S:
        case R_X86_64_64:
        case R_X86_64_GOTPC32:
        case R_X86_64_GOTPC64:
        case R_X86_64_GOTPCREL:
        case R_X86_64_GOTPCRELX:
        case R_X86_64_REX_GOTPCRELX:
        case R_X86_64_GOTTPOFF:
        case R_X86_64_GOT32:
        case R_X86_64_GOT64:
        case R_X86_64_GLOB_DAT:
        case R_X86_64_COPY:
        case R_X86_64_RELATIVE:
        case R_X86_64_GOTOFF64:
            return 0;

        case R_X86_64_PC32:
        case R_X86_64_PC64:
        case R_X86_64_PLT32:
        case R_X86_64_PLTOFF64:
        case R_X86_64_JUMP_SLOT:
            return 1;
    }

    tcc_error(-1, "Unknown relocation type: %d", reloc_type);
    return -1;
}

/* Returns an enumerator to describe whether and when the relocation needs a
   GOT and/or PLT entry to be created. See tcc.h for a description of the
   different values. */
int gotplt_entry_type (int reloc_type)
{
    switch (reloc_type) {
        case R_X86_64_GLOB_DAT:
        case R_X86_64_JUMP_SLOT:
        case R_X86_64_COPY:
        case R_X86_64_RELATIVE:
            return NO_GOTPLT_ENTRY;

	/* The following relocs wouldn't normally need GOT or PLT
	   slots, but we need them for simplicity in the link
	   editor part.  See our caller for comments.  */
        case R_X86_64_32:
        case R_X86_64_32S:
        case R_X86_64_64:
        case R_X86_64_PC32:
        case R_X86_64_PC64:
            return AUTO_GOTPLT_ENTRY;

        case R_X86_64_GOTTPOFF:
            return BUILD_GOT_ONLY;

        case R_X86_64_GOT32:
        case R_X86_64_GOT64:
        case R_X86_64_GOTPC32:
        case R_X86_64_GOTPC64:
        case R_X86_64_GOTOFF64:
        case R_X86_64_GOTPCREL:
        case R_X86_64_GOTPCRELX:
        case R_X86_64_REX_GOTPCRELX:
        case R_X86_64_PLT32:
        case R_X86_64_PLTOFF64:
            return ALWAYS_GOTPLT_ENTRY;
    }

    tcc_error(-1, "Unknown relocation type: %d", reloc_type);
    return -1;
}

ST_FUNC unsigned create_plt_entry(TCCState *s1, unsigned got_offset, struct sym_attr *attr)
{
    Section *plt = s1->plt;
    uint8_t *p;
    int modrm;
    unsigned plt_offset, relofs;

    modrm = 0x25;

    /* empty PLT: create PLT0 entry that pushes the library identifier
       (GOT + PTR_SIZE) and jumps to ld.so resolution routine
       (GOT + 2 * PTR_SIZE) */
    if (plt->data_offset == 0) {
        p = section_ptr_add(plt, 16);
        p[0] = 0xff; /* pushl got + PTR_SIZE */
        p[1] = modrm + 0x10;
        write32le(p + 2, PTR_SIZE);
        p[6] = 0xff; /* jmp *(got + PTR_SIZE * 2) */
        p[7] = modrm;
        write32le(p + 8, PTR_SIZE * 2);
    }
    plt_offset = plt->data_offset;

    /* The PLT slot refers to the relocation entry it needs via offset.
       The reloc entry is created below, so its offset is the current
       data_offset */
    relofs = s1->got->reloc ? s1->got->reloc->data_offset : 0;

    /* Jump to GOT entry where ld.so initially put the address of ip + 4 */
    p = section_ptr_add(plt, 16);
    p[0] = 0xff; /* jmp *(got + x) */
    p[1] = modrm;
    write32le(p + 2, got_offset);
    p[6] = 0x68; /* push $xxx */
    /* On x86-64, the relocation is referred to by _index_ */
    write32le(p + 7, relofs / sizeof (ElfW_Rel));
    p[11] = 0xe9; /* jmp plt_start */
    write32le(p + 12, -(plt->data_offset));
    return plt_offset;
}

/* relocate the PLT: compute addresses and offsets in the PLT now that final
   address for PLT and GOT are known (see fill_program_header) */
ST_FUNC void relocate_plt(TCCState *s1)
{
    uint8_t *p, *p_end;

    if (!s1->plt)
      return;

    p = s1->plt->data;
    p_end = p + s1->plt->data_offset;

    if (p < p_end) {
        int x = s1->got->sh_addr - s1->plt->sh_addr - 6;
        add32le(p + 2, x);
        add32le(p + 8, x - 6);
        p += 16;
        while (p < p_end) {
            add32le(p + 2, x + s1->plt->data - p);
            p += 16;
        }
    }
}

static ElfW_Rel *qrel; /* ptr to next reloc entry reused */

void relocate_init(Section *sr)
{
    qrel = (ElfW_Rel *) sr->data;
}

void relocate(TCCState *s1, ElfW_Rel *rel, int type, unsigned char *ptr, addr_t addr, addr_t val)
{
    int sym_index, esym_index;

    sym_index = ELFW(R_SYM)(rel->r_info);

    switch (type) {
        case R_X86_64_64:
            if (s1->output_type == TCC_OUTPUT_DLL) {
                esym_index = s1->sym_attrs[sym_index].dyn_index;
                qrel->r_offset = rel->r_offset;
                if (esym_index) {
                    qrel->r_info = ELFW(R_INFO)(esym_index, R_X86_64_64);
                    qrel->r_addend = rel->r_addend;
                    qrel++;
                    break;
                } else {
                    qrel->r_info = ELFW(R_INFO)(0, R_X86_64_RELATIVE);
                    qrel->r_addend = read64le(ptr) + val;
                    qrel++;
                }
            }
            add64le(ptr, val);
            break;
        case R_X86_64_32:
        case R_X86_64_32S:
            if (s1->output_type == TCC_OUTPUT_DLL) {
                /* XXX: this logic may depend on TCC's codegen
                   now TCC uses R_X86_64_32 even for a 64bit pointer */
                qrel->r_info = ELFW(R_INFO)(0, R_X86_64_RELATIVE);
                /* Use sign extension! */
                qrel->r_addend = (int)read32le(ptr) + val;
                qrel++;
            }
            add32le(ptr, val);
            break;

        case R_X86_64_PC32:
            if (s1->output_type == TCC_OUTPUT_DLL) {
                /* DLL relocation */
                esym_index = s1->sym_attrs[sym_index].dyn_index;
                if (esym_index) {
                    qrel->r_offset = rel->r_offset;
                    qrel->r_info = ELFW(R_INFO)(esym_index, R_X86_64_PC32);
                    /* Use sign extension! */
                    qrel->r_addend = (int)read32le(ptr) + rel->r_addend;
                    qrel++;
                    break;
                }
            }
            goto plt32pc32;

        case R_X86_64_PLT32:
            /* fallthrough: val already holds the PLT slot address */

        plt32pc32:
        {
            long long diff;
            diff = (long long)val - addr;
            if (diff < -2147483648LL || diff > 2147483647LL) {
                tcc_error(-1, "internal error: relocation failed");
            }
            add32le(ptr, diff);
        }
            break;

        case R_X86_64_PLTOFF64:
            add64le(ptr, val - s1->got->sh_addr + rel->r_addend);
            break;

        case R_X86_64_PC64:
            if (s1->output_type == TCC_OUTPUT_DLL) {
                /* DLL relocation */
                esym_index = s1->sym_attrs[sym_index].dyn_index;
                if (esym_index) {
                    qrel->r_offset = rel->r_offset;
                    qrel->r_info = ELFW(R_INFO)(esym_index, R_X86_64_PC64);
                    qrel->r_addend = read64le(ptr) + rel->r_addend;
                    qrel++;
                    break;
                }
            }
            add64le(ptr, val - addr);
            break;

        case R_X86_64_GLOB_DAT:
        case R_X86_64_JUMP_SLOT:
            /* They don't need addend */
            write64le(ptr, val - rel->r_addend);
            break;
        case R_X86_64_GOTPCREL:
        case R_X86_64_GOTPCRELX:
        case R_X86_64_REX_GOTPCRELX:
            add32le(ptr, s1->got->sh_addr - addr +
                         s1->sym_attrs[sym_index].got_offset - 4);
            break;
        case R_X86_64_GOTPC32:
            add32le(ptr, s1->got->sh_addr - addr + rel->r_addend);
            break;
        case R_X86_64_GOTPC64:
            add64le(ptr, s1->got->sh_addr - addr + rel->r_addend);
            break;
        case R_X86_64_GOTTPOFF:
            add32le(ptr, val - s1->got->sh_addr);
            break;
        case R_X86_64_GOT32:
            /* we load the got offset */
            add32le(ptr, s1->sym_attrs[sym_index].got_offset);
            break;
        case R_X86_64_GOT64:
            /* we load the got offset */
            add64le(ptr, s1->sym_attrs[sym_index].got_offset);
            break;
        case R_X86_64_GOTOFF64:
            add64le(ptr, val - s1->got->sh_addr);
            break;
        case R_X86_64_RELATIVE:
#ifdef TCC_TARGET_PE
            add32le(ptr, val - s1->pe_imagebase);
#endif
            /* do nothing */
            break;
    }
}

#endif  /* #ifdef TCC_TARGET_X86_64 */

#if defined( TCC_TARGET_I386 ) || defined( TCC_TARGET_X86_64 )

/*  i386 specific functions for TCC assembler
 *  Copyright (c) 2001, 2002 Fabrice Bellard
 *  Copyright (c) 2009 Frédéric Feret (x86_64 support)
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */

#define MAX_OPERANDS 3

#define TOK_ASM_first TOK_ASM_clc
#define TOK_ASM_last TOK_ASM_emms
#define TOK_ASM_alllast TOK_ASM_subps

#define OPC_B          0x01  /* only used with OPC_WL */
#define OPC_WL         0x02  /* accepts w, l or no suffix */
#define OPC_BWL        (OPC_B | OPC_WL) /* accepts b, w, l or no suffix */
#define OPC_REG        0x04 /* register is added to opcode */
#define OPC_MODRM      0x08 /* modrm encoding */

#define OPCT_MASK      0x70
#define OPC_FWAIT      0x10 /* add fwait opcode */
#define OPC_SHIFT      0x20 /* shift opcodes */
#define OPC_ARITH      0x30 /* arithmetic opcodes */
#define OPC_FARITH     0x40 /* FPU arithmetic opcodes */
#define OPC_TEST       0x50 /* test opcodes */
#define OPCT_IS(v,i) (((v) & OPCT_MASK) == (i))

#define OPC_0F        0x100 /* Is secondary map (0x0f prefix) */
#define OPC_48        0x200 /* Always has REX prefix */
#ifdef TCC_TARGET_X86_64
# define OPC_WLQ     0x1000  /* accepts w, l, q or no suffix */
# define OPC_BWLQ    (OPC_B | OPC_WLQ) /* accepts b, w, l, q or no suffix */
# define OPC_WLX     OPC_WLQ
# define OPC_BWLX    OPC_BWLQ
#else
# define OPC_WLX     OPC_WL
# define OPC_BWLX    OPC_BWL
#endif

#define OPC_GROUP_SHIFT 13

/* in order to compress the operand type, we use specific operands and
   we or only with EA  */
enum {
    OPT_REG8=0, /* warning: value is hardcoded from TOK_ASM_xxx */
    OPT_REG16,  /* warning: value is hardcoded from TOK_ASM_xxx */
    OPT_REG32,  /* warning: value is hardcoded from TOK_ASM_xxx */
#ifdef TCC_TARGET_X86_64
    OPT_REG64,  /* warning: value is hardcoded from TOK_ASM_xxx */
#endif
    OPT_MMX,    /* warning: value is hardcoded from TOK_ASM_xxx */
    OPT_SSE,    /* warning: value is hardcoded from TOK_ASM_xxx */
    OPT_CR,     /* warning: value is hardcoded from TOK_ASM_xxx */
    OPT_TR,     /* warning: value is hardcoded from TOK_ASM_xxx */
    OPT_DB,     /* warning: value is hardcoded from TOK_ASM_xxx */
    OPT_SEG,
    OPT_ST,
#ifdef TCC_TARGET_X86_64
    OPT_REG8_LOW, /* %spl,%bpl,%sil,%dil, encoded like ah,ch,dh,bh, but
		     with REX prefix, not used in insn templates */
#endif
    OPT_IM8,
    OPT_IM8S,
    OPT_IM16,
    OPT_IM32,
#ifdef TCC_TARGET_X86_64
    OPT_IM64,
#endif
    OPT_EAX,    /* %al, %ax, %eax or %rax register */
    OPT_ST0,    /* %st(0) register */
    OPT_CL,     /* %cl register */
    OPT_DX,     /* %dx register */
    OPT_ADDR,   /* OP_EA with only offset */
    OPT_INDIR,  /* *(expr) */
    /* composite types */
    OPT_COMPOSITE_FIRST,
    OPT_IM,     /* IM8 | IM16 | IM32 */
    OPT_REG,    /* REG8 | REG16 | REG32 | REG64 */
    OPT_REGW,   /* REG16 | REG32 | REG64 */
    OPT_IMW,    /* IM16 | IM32 */
    OPT_MMXSSE, /* MMX | SSE */
    OPT_DISP,   /* Like OPT_ADDR, but emitted as displacement (for jumps) */
    OPT_DISP8,  /* Like OPT_ADDR, but only 8bit (short jumps) */
    /* can be ored with any OPT_xxx */
    OPT_EA = 0x80
};

#define OP_REG8   (1 << OPT_REG8)
#define OP_REG16  (1 << OPT_REG16)
#define OP_REG32  (1 << OPT_REG32)
#define OP_MMX    (1 << OPT_MMX)
#define OP_SSE    (1 << OPT_SSE)
#define OP_CR     (1 << OPT_CR)
#define OP_TR     (1 << OPT_TR)
#define OP_DB     (1 << OPT_DB)
#define OP_SEG    (1 << OPT_SEG)
#define OP_ST     (1 << OPT_ST)
#define OP_IM8    (1 << OPT_IM8)
#define OP_IM8S   (1 << OPT_IM8S)
#define OP_IM16   (1 << OPT_IM16)
#define OP_IM32   (1 << OPT_IM32)
#define OP_EAX    (1 << OPT_EAX)
#define OP_ST0    (1 << OPT_ST0)
#define OP_CL     (1 << OPT_CL)
#define OP_DX     (1 << OPT_DX)
#define OP_ADDR   (1 << OPT_ADDR)
#define OP_INDIR  (1 << OPT_INDIR)
#ifdef TCC_TARGET_X86_64
# define OP_REG64 (1 << OPT_REG64)
# define OP_REG8_LOW (1 << OPT_REG8_LOW)
# define OP_IM64  (1 << OPT_IM64)
# define OP_EA32  (OP_EA << 1)
#else
# define OP_REG64 0
# define OP_REG8_LOW 0
# define OP_IM64  0
# define OP_EA32  0
#endif

#define OP_EA     0x40000000
#define OP_REG    (OP_REG8 | OP_REG16 | OP_REG32 | OP_REG64)

#ifdef TCC_TARGET_X86_64
# define TREG_XAX   TREG_RAX
# define TREG_XCX   TREG_RCX
# define TREG_XDX   TREG_RDX
#else
# define TREG_XAX   TREG_EAX
# define TREG_XCX   TREG_ECX
# define TREG_XDX   TREG_EDX
#endif

typedef struct ASMInstr {
    uint16_t sym;
    uint16_t opcode;
    uint16_t instr_type;
    uint8_t nb_ops;
    uint8_t op_type[MAX_OPERANDS]; /* see OP_xxx */
} ASMInstr;

typedef struct Operand {
    uint32_t type;
    int8_t  reg; /* register, -1 if none */
    int8_t  reg2; /* second register, -1 if none */
    uint8_t shift;
    ExprValue e;
} Operand;

static const uint8_t reg_to_size[9] = {
/*
    [OP_REG8] = 0,
    [OP_REG16] = 1,
    [OP_REG32] = 2,
#ifdef TCC_TARGET_X86_64
    [OP_REG64] = 3,
#endif
*/
    0, 0, 1, 0, 2, 0, 0, 0, 3
};

#define NB_TEST_OPCODES 30

static const uint8_t test_bits[NB_TEST_OPCODES] = {
 0x00, /* o */
 0x01, /* no */
 0x02, /* b */
 0x02, /* c */
 0x02, /* nae */
 0x03, /* nb */
 0x03, /* nc */
 0x03, /* ae */
 0x04, /* e */
 0x04, /* z */
 0x05, /* ne */
 0x05, /* nz */
 0x06, /* be */
 0x06, /* na */
 0x07, /* nbe */
 0x07, /* a */
 0x08, /* s */
 0x09, /* ns */
 0x0a, /* p */
 0x0a, /* pe */
 0x0b, /* np */
 0x0b, /* po */
 0x0c, /* l */
 0x0c, /* nge */
 0x0d, /* nl */
 0x0d, /* ge */
 0x0e, /* le */
 0x0e, /* ng */
 0x0f, /* nle */
 0x0f, /* g */
};

static const uint8_t segment_prefixes[] = {
 0x26, /* es */
 0x2e, /* cs */
 0x36, /* ss */
 0x3e, /* ds */
 0x64, /* fs */
 0x65  /* gs */
};

static const ASMInstr asm_instrs[] = {
#define ALT(x) x
/* This removes a 0x0f in the second byte */
#define O(o) ((uint64_t) ((((o) & 0xff00) == 0x0f00) ? ((((o) >> 8) & ~0xff) | ((o) & 0xff)) : (o)))
/* This constructs instr_type from opcode, type and group.  */
#define T(o,i,g) ((i) | ((g) << OPC_GROUP_SHIFT) | ((((o) & 0xff00) == 0x0f00) ? OPC_0F : 0))
#define DEF_ASM_OP0(name, opcode)
#define DEF_ASM_OP0L(name, opcode, group, instr_type) { TOK_ASM_ ## name, O(opcode), T(opcode, instr_type, group), 0, { 0 } },
#define DEF_ASM_OP1(name, opcode, group, instr_type, op0) { TOK_ASM_ ## name, O(opcode), T(opcode, instr_type, group), 1, { op0 }},
#define DEF_ASM_OP2(name, opcode, group, instr_type, op0, op1) { TOK_ASM_ ## name, O(opcode), T(opcode, instr_type, group), 2, { op0, op1 }},
#define DEF_ASM_OP3(name, opcode, group, instr_type, op0, op1, op2) { TOK_ASM_ ## name, O(opcode), T(opcode, instr_type, group), 3, { op0, op1, op2 }},
#ifdef TCC_TARGET_X86_64
# include "x86_64-asm.h"
#else
# include "i386-asm.h"
#endif
    /* last operation */
    { 0, },
};

static const uint16_t op0_codes[] = {
#define ALT(x)
#define DEF_ASM_OP0(x, opcode) opcode,
#define DEF_ASM_OP0L(name, opcode, group, instr_type)
#define DEF_ASM_OP1(name, opcode, group, instr_type, op0)
#define DEF_ASM_OP2(name, opcode, group, instr_type, op0, op1)
#define DEF_ASM_OP3(name, opcode, group, instr_type, op0, op1, op2)
#ifdef TCC_TARGET_X86_64
# include "x86_64-asm.h"
#else
# include "i386-asm.h"
#endif
};

static inline int get_reg_shift(TCCState *s1)
{
    int shift, v;
    v = asm_int_expr(s1);
    switch(v) {
    case 1:
        shift = 0;
        break;
    case 2:
        shift = 1;
        break;
    case 4:
        shift = 2;
        break;
    case 8:
        shift = 3;
        break;
    default:
        tcc_error(-1, "1, 2, 4 or 8 constant expected" );
        shift = 0;
        break;
    }
    return shift;
}

#ifdef TCC_TARGET_X86_64
static int asm_parse_numeric_reg(int t, unsigned int *type)
{
    int reg = -1;
    if (t >= TOK_IDENT && t < tok_ident) {
	const char *s = table_ident[t - TOK_IDENT]->str;
	char c;
	*type = OP_REG64;
	if (*s == 'c') {
	    s++;
	    *type = OP_CR;
	}
	if (*s++ != 'r')
	  return -1;
	/* Don't allow leading '0'.  */
	if ((c = *s++) >= '1' && c <= '9')
	  reg = c - '0';
	else
	  return -1;
	if ((c = *s) >= '0' && c <= '5')
	  s++, reg = reg * 10 + c - '0';
	if (reg > 15)
	  return -1;
	if ((c = *s) == 0)
	  ;
	else if (*type != OP_REG64)
	  return -1;
	else if (c == 'b' && !s[1])
	  *type = OP_REG8;
	else if (c == 'w' && !s[1])
	  *type = OP_REG16;
	else if (c == 'd' && !s[1])
	  *type = OP_REG32;
	else
	  return -1;
    }
    return reg;
}
#endif

static int asm_parse_reg(unsigned int *type)
{
    int reg = 0;
    *type = 0;
    if (tok != '%')
        goto error_32;
    next();
    if (tok >= TOK_ASM_eax && tok <= TOK_ASM_edi) {
        reg = tok - TOK_ASM_eax;
	*type = OP_REG32;
#ifdef TCC_TARGET_X86_64
    } else if (tok >= TOK_ASM_rax && tok <= TOK_ASM_rdi) {
        reg = tok - TOK_ASM_rax;
	*type = OP_REG64;
    } else if (tok == TOK_ASM_rip) {
        reg = -2; /* Probably should use different escape code. */
	*type = OP_REG64;
    } else if ((reg = asm_parse_numeric_reg(tok, type)) >= 0
	       && (*type == OP_REG32 || *type == OP_REG64)) {
	;
#endif
    }
    else {
    error_32:
        tcc_error(-1, "register expected" );
    }
    next();
    return reg;
}

static void parse_operand(TCCState *s1, Operand *op)
{
    ExprValue e;
    int reg, indir;
    const char *p;

    indir = 0;
    if (tok == '*') {
        next();
        indir = OP_INDIR;
    }

    if (tok == '%') {
        next();
        if (tok >= TOK_ASM_al && tok <= TOK_ASM_db7) {
            reg = tok - TOK_ASM_al;
            op->type = 1 << (reg >> 3); /* WARNING: do not change constant order */
            op->reg = reg & 7;
            if ((op->type & OP_REG) && op->reg == TREG_XAX)
                op->type |= OP_EAX;
            else if (op->type == OP_REG8 && op->reg == TREG_XCX)
                op->type |= OP_CL;
            else if (op->type == OP_REG16 && op->reg == TREG_XDX)
                op->type |= OP_DX;
        } else if (tok >= TOK_ASM_dr0 && tok <= TOK_ASM_dr7) {
            op->type = OP_DB;
            op->reg = tok - TOK_ASM_dr0;
        } else if (tok >= TOK_ASM_es && tok <= TOK_ASM_gs) {
            op->type = OP_SEG;
            op->reg = tok - TOK_ASM_es;
        } else if (tok == TOK_ASM_st) {
            op->type = OP_ST;
            op->reg = 0;
            next();
            if (tok == '(') {
                next();
                if (tok != TOK_PPNUM)
                    goto reg_error;
                p = tokc.str.data;
                reg = p[0] - '0';
                if ((unsigned)reg >= 8 || p[1] != '\0')
                    goto reg_error;
                op->reg = reg;
                next();
                skip(')');
            }
            if (op->reg == 0)
                op->type |= OP_ST0;
            goto no_skip;
#ifdef TCC_TARGET_X86_64
	} else if (tok >= TOK_ASM_spl && tok <= TOK_ASM_dil) {
	    op->type = OP_REG8 | OP_REG8_LOW;
	    op->reg = 4 + tok - TOK_ASM_spl;
        } else if ((op->reg = asm_parse_numeric_reg(tok, &op->type)) >= 0) {
	    ;
#endif
        } else {
        reg_error:
            tcc_error(-1, "unknown register %%%s", get_tok_str(tok, &tokc));
        }
        next();
    no_skip: ;
    } else if (tok == '$') {
        /* constant value */
        next();
        asm_expr(s1, &e);
        op->type = OP_IM32;
        op->e = e;
        if (!op->e.sym) {
            if (op->e.v == (uint8_t)op->e.v)
                op->type |= OP_IM8;
            if (op->e.v == (int8_t)op->e.v)
                op->type |= OP_IM8S;
            if (op->e.v == (uint16_t)op->e.v)
                op->type |= OP_IM16;
#ifdef TCC_TARGET_X86_64
            if (op->e.v != (int32_t)op->e.v && op->e.v != (uint32_t)op->e.v)
                op->type = OP_IM64;
#endif
        }
    } else {
        /* address(reg,reg2,shift) with all variants */
        op->type = OP_EA;
        op->reg = -1;
        op->reg2 = -1;
        op->shift = 0;
        if (tok != '(') {
            asm_expr(s1, &e);
            op->e = e;
        } else {
            next();
            if (tok == '%') {
                unget_tok('(');
                op->e.v = 0;
                op->e.sym = NULL;
            } else {
                /* bracketed offset expression */
                asm_expr(s1, &e);
                if( tok != ')' )  tcc_error(-1, ") expected" );
                next();
                op->e.v = e.v;
                op->e.sym = e.sym;
            }
	    op->e.pcrel = 0;
        }
        if (tok == '(') {
	    unsigned int type = 0;
            next();
            if (tok != ',') {
                op->reg = asm_parse_reg(&type);
            }
            if (tok == ',') {
                next();
                if (tok != ',') {
                    op->reg2 = asm_parse_reg(&type);
                }
                if (tok == ',') {
                    next();
                    op->shift = get_reg_shift(s1);
                }
            }
	    if (type & OP_REG32)
	        op->type |= OP_EA32;
            skip(')');
        }
        if (op->reg == -1 && op->reg2 == -1)
            op->type |= OP_ADDR;
    }
    op->type |= indir;
}

/* XXX: unify with C code output ? */
ST_FUNC void gen_expr32(ExprValue *pe)
{
    if (pe->pcrel)
        /* If PC-relative, always set VT_SYM, even without symbol,
	   so as to force a relocation to be emitted.  */
	gen_addrpc32(VT_SYM, pe->sym, pe->v);
    else
	gen_addr32(pe->sym ? VT_SYM : 0, pe->sym, pe->v);
}

#ifdef TCC_TARGET_X86_64
ST_FUNC void gen_expr64(ExprValue *pe)
{
    gen_addr64(pe->sym ? VT_SYM : 0, pe->sym, pe->v);
}
#endif

/* XXX: unify with C code output ? */
static void gen_disp32(ExprValue *pe)
{
    Sym *sym = pe->sym;
    ElfSym *esym = elfsym(sym);
    if (esym && esym->st_shndx == cur_text_section->sh_num) {
        /* same section: we can output an absolute value. Note
           that the TCC compiler behaves differently here because
           it always outputs a relocation to ease (future) code
           elimination in the linker */
        gen_le32(pe->v + esym->st_value - ind - 4);
    } else {
        if (sym && sym->type.t == VT_VOID) {
            sym->type.t = VT_FUNC;
            sym->type.ref = NULL;
        }
        gen_addrpc32(VT_SYM, sym, pe->v);
    }
}

/* generate the modrm operand */
static inline int asm_modrm(int reg, Operand *op)
{
    int mod, reg1, reg2, sib_reg1;

    if (op->type & (OP_REG | OP_MMX | OP_SSE)) {
        g(0xc0 + (reg << 3) + op->reg);
    } else if (op->reg == -1 && op->reg2 == -1) {
        /* displacement only */
#ifdef TCC_TARGET_X86_64
	g(0x04 + (reg << 3));
	g(0x25);
#else
	g(0x05 + (reg << 3));
#endif
	gen_expr32(&op->e);
#ifdef TCC_TARGET_X86_64
    } else if (op->reg == -2) {
        ExprValue *pe = &op->e;
        g(0x05 + (reg << 3));
        gen_addrpc32(pe->sym ? VT_SYM : 0, pe->sym, pe->v);
        return ind;
#endif
    } else {
        sib_reg1 = op->reg;
        /* fist compute displacement encoding */
        if (sib_reg1 == -1) {
            sib_reg1 = 5;
            mod = 0x00;
        } else if (op->e.v == 0 && !op->e.sym && op->reg != 5) {
            mod = 0x00;
        } else if (op->e.v == (int8_t)op->e.v && !op->e.sym) {
            mod = 0x40;
        } else {
            mod = 0x80;
        }
        /* compute if sib byte needed */
        reg1 = op->reg;
        if (op->reg2 != -1)
            reg1 = 4;
        g(mod + (reg << 3) + reg1);
        if (reg1 == 4) {
            /* add sib byte */
            reg2 = op->reg2;
            if (reg2 == -1)
                reg2 = 4; /* indicate no index */
            g((op->shift << 6) + (reg2 << 3) + sib_reg1);
        }
        /* add offset */
        if (mod == 0x40) {
            g(op->e.v);
        } else if (mod == 0x80 || op->reg == -1) {
	    gen_expr32(&op->e);
        }
    }
    return 0;
}

#ifdef TCC_TARGET_X86_64
#define REX_W 0x48
#define REX_R 0x44
#define REX_X 0x42
#define REX_B 0x41

static void asm_rex(int width64, Operand *ops, int nb_ops, int *op_type,
		    int regi, int rmi)
{
  unsigned char rex = width64 ? 0x48 : 0;
  int saw_high_8bit = 0;
  int i;
  if (rmi == -1) {
      /* No mod/rm byte, but we might have a register op nevertheless
         (we will add it to the opcode later).  */
      for(i = 0; i < nb_ops; i++) {
	  if (op_type[i] & (OP_REG | OP_ST)) {
	      if (ops[i].reg >= 8) {
		  rex |= REX_B;
		  ops[i].reg -= 8;
	      } else if (ops[i].type & OP_REG8_LOW)
		  rex |= 0x40;
	      else if (ops[i].type & OP_REG8 && ops[i].reg >= 4)
		  /* An 8 bit reg >= 4 without REG8 is ah/ch/dh/bh */
		  saw_high_8bit = ops[i].reg;
	      break;
	  }
      }
  } else {
      if (regi != -1) {
	  if (ops[regi].reg >= 8) {
	      rex |= REX_R;
	      ops[regi].reg -= 8;
	  } else if (ops[regi].type & OP_REG8_LOW)
	      rex |= 0x40;
	  else if (ops[regi].type & OP_REG8 && ops[regi].reg >= 4)
	      /* An 8 bit reg >= 4 without REG8 is ah/ch/dh/bh */
	      saw_high_8bit = ops[regi].reg;
      }
      if (ops[rmi].type & (OP_REG | OP_MMX | OP_SSE | OP_CR | OP_EA)) {
	  if (ops[rmi].reg >= 8) {
	      rex |= REX_B;
	      ops[rmi].reg -= 8;
	  } else if (ops[rmi].type & OP_REG8_LOW)
	      rex |= 0x40;
	  else if (ops[rmi].type & OP_REG8 && ops[rmi].reg >= 4)
	      /* An 8 bit reg >= 4 without REG8 is ah/ch/dh/bh */
	      saw_high_8bit = ops[rmi].reg;
      }
      if (ops[rmi].type & OP_EA && ops[rmi].reg2 >= 8) {
	  rex |= REX_X;
	  ops[rmi].reg2 -= 8;
      }
  }
  if (rex) {
      if (saw_high_8bit)
	  tcc_error(-1, "can't encode register %%%ch when REX prefix is required", "acdb"[saw_high_8bit-4]);
      g(rex);
  }
}
#endif

static void maybe_print_stats (void)
{
  static int already = 1;
  if (!already)
    /* print stats about opcodes */
    {
        const struct ASMInstr *pa;
        int freq[4];
        int op_vals[500];
        int nb_op_vals, i, j;

	already = 1;
        nb_op_vals = 0;
        memset(freq, 0, sizeof(freq));
        for(pa = asm_instrs; pa->sym != 0; pa++) {
            freq[pa->nb_ops]++;
            //for(i=0;i<pa->nb_ops;i++) {
                for(j=0;j<nb_op_vals;j++) {
                    //if (pa->op_type[i] == op_vals[j])
                    if (pa->instr_type == op_vals[j])
                        goto found;
                }
                //op_vals[nb_op_vals++] = pa->op_type[i];
                op_vals[nb_op_vals++] = pa->instr_type;
            found: ;
            //}
        }
        for(i=0;i<nb_op_vals;i++) {
            int v = op_vals[i];
            //if ((v & (v - 1)) != 0)
                printf("%3d: %08x\n", i, v);
        }
        printf("size=%d nb=%d f0=%d f1=%d f2=%d f3=%d\n",
               (int)sizeof(asm_instrs),
	       (int)sizeof(asm_instrs) / (int)sizeof(ASMInstr),
               freq[0], freq[1], freq[2], freq[3]);
    }
}

ST_FUNC void asm_opcode(TCCState *s1, int opcode)
{
    const ASMInstr *pa;
    int i, modrm_index, modreg_index, reg, v, op1, seg_prefix, pc;
    int nb_ops, s;
    Operand ops[MAX_OPERANDS], *pop;
    int op_type[3]; /* decoded op type */
    int alltypes;   /* OR of all operand types */
    int autosize;
    int p66;
#ifdef TCC_TARGET_X86_64
    int rex64;
#endif

    maybe_print_stats();
    /* force synthetic ';' after prefix instruction, so we can handle */
    /* one-line things like "rep stosb" instead of only "rep\nstosb" */
    if (opcode >= TOK_ASM_wait && opcode <= TOK_ASM_repnz)
        unget_tok(';');

    /* get operands */
    pop = ops;
    nb_ops = 0;
    seg_prefix = 0;
    alltypes = 0;
    for(;;) {
        if (tok == ';' || tok == TOK_LINEFEED)
            break;
        if( nb_ops >= MAX_OPERANDS )  tcc_error(-1, "incorrect number of operands");
        parse_operand(s1, pop);
        if (tok == ':') {
           if( pop->type != OP_SEG || seg_prefix )  tcc_error(-1, "incorrect prefix");
           seg_prefix = segment_prefixes[pop->reg];
           next();
           parse_operand(s1, pop);
           if (!(pop->type & OP_EA)) {
               tcc_error(-1, "segment prefix must be followed by memory reference");
           }
        }
        pop++;
        nb_ops++;
        if (tok != ',')
            break;
        next();
    }

    s = 0; /* avoid warning */

again:
    /* optimize matching by using a lookup table (no hashing is needed
       !) */
    for(pa = asm_instrs; pa->sym != 0; pa++) {
	int it = pa->instr_type & OPCT_MASK;
        s = 0;
        if (it == OPC_FARITH) {
            v = opcode - pa->sym;
            if (!((unsigned)v < 8 * 6 && (v % 6) == 0))
                continue;
        } else if (it == OPC_ARITH) {
            if (!(opcode >= pa->sym && opcode < pa->sym + 8*NBWLX))
                continue;
            s = (opcode - pa->sym) % NBWLX;
	    if ((pa->instr_type & OPC_BWLX) == OPC_WLX)
	      {
		/* We need to reject the xxxb opcodes that we accepted above.
		   Note that pa->sym for WLX opcodes is the 'w' token,
		   to get the 'b' token subtract one.  */
		if (((opcode - pa->sym + 1) % NBWLX) == 0)
		    continue;
	        s++;
	      }
        } else if (it == OPC_SHIFT) {
            if (!(opcode >= pa->sym && opcode < pa->sym + 7*NBWLX))
                continue;
            s = (opcode - pa->sym) % NBWLX;
        } else if (it == OPC_TEST) {
            if (!(opcode >= pa->sym && opcode < pa->sym + NB_TEST_OPCODES))
                continue;
	    /* cmovxx is a test opcode but accepts multiple sizes.
	       The suffixes aren't encoded in the table, instead we
	       simply force size autodetection always and deal with suffixed
	       variants below when we don't find e.g. "cmovzl".  */
	    if (pa->instr_type & OPC_WLX)
	        s = NBWLX - 1;
        } else if (pa->instr_type & OPC_B) {
#ifdef TCC_TARGET_X86_64
	    /* Some instructions don't have the full size but only
	       bwl form.  insb e.g. */
	    if ((pa->instr_type & OPC_WLQ) != OPC_WLQ
		&& !(opcode >= pa->sym && opcode < pa->sym + NBWLX-1))
	        continue;
#endif
            if (!(opcode >= pa->sym && opcode < pa->sym + NBWLX))
                continue;
            s = opcode - pa->sym;
        } else if (pa->instr_type & OPC_WLX) {
            if (!(opcode >= pa->sym && opcode < pa->sym + NBWLX-1))
                continue;
            s = opcode - pa->sym + 1;
        } else {
            if (pa->sym != opcode)
                continue;
        }
        if (pa->nb_ops != nb_ops)
            continue;
#ifdef TCC_TARGET_X86_64
	/* Special case for moves.  Selecting the IM64->REG64 form
	   should only be done if we really have an >32bit imm64, and that
	   is hardcoded.  Ignore it here.  */
	if (pa->opcode == 0xb0 && ops[0].type != OP_IM64
	    && (ops[1].type & OP_REG) == OP_REG64
	    && !(pa->instr_type & OPC_0F))
	    continue;
#endif
        /* now decode and check each operand */
	alltypes = 0;
        for(i = 0; i < nb_ops; i++) {
            int op1, op2;
            op1 = pa->op_type[i];
            op2 = op1 & 0x1f;
            switch(op2) {
            case OPT_IM:
                v = OP_IM8 | OP_IM16 | OP_IM32;
                break;
            case OPT_REG:
                v = OP_REG8 | OP_REG16 | OP_REG32 | OP_REG64;
                break;
            case OPT_REGW:
                v = OP_REG16 | OP_REG32 | OP_REG64;
                break;
            case OPT_IMW:
                v = OP_IM16 | OP_IM32;
                break;
	    case OPT_MMXSSE:
		v = OP_MMX | OP_SSE;
		break;
	    case OPT_DISP:
	    case OPT_DISP8:
		v = OP_ADDR;
		break;
            default:
                v = 1 << op2;
                break;
            }
            if (op1 & OPT_EA)
                v |= OP_EA;
	    op_type[i] = v;
            if ((ops[i].type & v) == 0)
                goto next;
	    alltypes |= ops[i].type;
        }
        /* all is matching ! */
        break;
    next: ;
    }
    if (pa->sym == 0) {
        if (opcode >= TOK_ASM_first && opcode <= TOK_ASM_last) {
            int b;
            b = op0_codes[opcode - TOK_ASM_first];
            if (b & 0xff00) 
                g(b >> 8);
            g(b);
            return;
        } else if (opcode <= TOK_ASM_alllast) {
            tcc_error(-1, "bad operand with opcode '%s'", get_tok_str(opcode, NULL));
        } else {
	    /* Special case for cmovcc, we accept size suffixes but ignore
	       them, but we don't want them to blow up our tables.  */
	    TokenSym *ts = table_ident[opcode - TOK_IDENT];
	    if (ts->len >= 6
		&& strchr("wlq", ts->str[ts->len-1])
		&& !memcmp(ts->str, "cmov", 4)) {
		opcode = tok_alloc(ts->str, ts->len-1)->tok;
		goto again;
	    }
            tcc_error(-1, "unknown opcode '%s'", ts->str);
        }
    }
    /* if the size is unknown, then evaluate it (OPC_B or OPC_WL case) */
    autosize = NBWLX-1;
#ifdef TCC_TARGET_X86_64
    /* XXX the autosize should rather be zero, to not have to adjust this
       all the time.  */
    if ((pa->instr_type & OPC_BWLQ) == OPC_B)
        autosize = NBWLX-2;
#endif
    if (s == autosize) {
	/* Check for register operands providing hints about the size.
	   Start from the end, i.e. destination operands.  This matters
	   only for opcodes accepting different sized registers, lar and lsl
	   are such opcodes.  */
        for(i = nb_ops - 1; s == autosize && i >= 0; i--) {
            if ((ops[i].type & OP_REG) && !(op_type[i] & (OP_CL | OP_DX)))
                s = reg_to_size[ops[i].type & OP_REG];
        }
        if (s == autosize) {
            if ((opcode == TOK_ASM_push || opcode == TOK_ASM_pop) &&
                (ops[0].type & (OP_SEG | OP_IM8S | OP_IM32)))
                s = 2;
	    else if ((opcode == TOK_ASM_push || opcode == TOK_ASM_pop) &&
		     (ops[0].type & OP_EA))
	        s = NBWLX - 2;
            else  tcc_error(-1, "cannot infer opcode suffix");
        }
    }

#ifdef TCC_TARGET_X86_64
    /* Generate addr32 prefix if needed */
    for(i = 0; i < nb_ops; i++) {
        if (ops[i].type & OP_EA32) {
	    g(0x67);
	    break;
        }
    }
#endif
    /* generate data16 prefix if needed */
    p66 = 0;
    if (s == 1)
        p66 = 1;
    else {
	/* accepting mmx+sse in all operands --> needs 0x66 to
	   switch to sse mode.  Accepting only sse in an operand --> is
	   already SSE insn and needs 0x66/f2/f3 handling.  */
        for (i = 0; i < nb_ops; i++)
            if ((op_type[i] & (OP_MMX | OP_SSE)) == (OP_MMX | OP_SSE)
	        && ops[i].type & OP_SSE)
	        p66 = 1;
    }
    if (p66)
        g(0x66);
#ifdef TCC_TARGET_X86_64
    rex64 = 0;
    if (pa->instr_type & OPC_48)
        rex64 = 1;
    else if (s == 3 || (alltypes & OP_REG64)) {
        /* generate REX prefix */
	int default64 = 0;
	for(i = 0; i < nb_ops; i++) {
	    if (op_type[i] == OP_REG64 && pa->opcode != 0xb8) {
		/* If only 64bit regs are accepted in one operand
		   this is a default64 instruction without need for
		   REX prefixes, except for movabs(0xb8).  */
		default64 = 1;
		break;
	    }
	}
	/* XXX find better encoding for the default64 instructions.  */
        if (((opcode != TOK_ASM_push && opcode != TOK_ASM_pop
	      && opcode != TOK_ASM_pushw && opcode != TOK_ASM_pushl
	      && opcode != TOK_ASM_pushq && opcode != TOK_ASM_popw
	      && opcode != TOK_ASM_popl && opcode != TOK_ASM_popq
	      && opcode != TOK_ASM_call && opcode != TOK_ASM_jmp))
	    && !default64)
            rex64 = 1;
    }
#endif

    /* now generates the operation */
    if (OPCT_IS(pa->instr_type, OPC_FWAIT))
        g(0x9b);
    if (seg_prefix)
        g(seg_prefix);

    v = pa->opcode;
    if (pa->instr_type & OPC_0F)
        v = ((v & ~0xff) << 8) | 0x0f00 | (v & 0xff);
    if ((v == 0x69 || v == 0x6b) && nb_ops == 2) {
        /* kludge for imul $im, %reg */
        nb_ops = 3;
        ops[2] = ops[1];
        op_type[2] = op_type[1];
    } else if (v == 0xcd && ops[0].e.v == 3 && !ops[0].e.sym) {
        v--; /* int $3 case */
        nb_ops = 0;
    } else if ((v == 0x06 || v == 0x07)) {
        if (ops[0].reg >= 4) {
            /* push/pop %fs or %gs */
            v = 0x0fa0 + (v - 0x06) + ((ops[0].reg - 4) << 3);
        } else {
            v += ops[0].reg << 3;
        }
        nb_ops = 0;
    } else if (v <= 0x05) {
        /* arith case */
        v += ((opcode - TOK_ASM_addb) / NBWLX) << 3;
    } else if ((pa->instr_type & (OPCT_MASK | OPC_MODRM)) == OPC_FARITH) {
        /* fpu arith case */
        v += ((opcode - pa->sym) / 6) << 3;
    }

    /* search which operand will be used for modrm */
    modrm_index = -1;
    modreg_index = -1;
    if (pa->instr_type & OPC_MODRM) {
	if (!nb_ops) {
	    /* A modrm opcode without operands is a special case (e.g. mfence).
	       It has a group and acts as if there's an register operand 0
	       (ax).  */
	    i = 0;
	    ops[i].type = OP_REG;
	    ops[i].reg = 0;
	    goto modrm_found;
	}
        /* first look for an ea operand */
        for(i = 0;i < nb_ops; i++) {
            if (op_type[i] & OP_EA)
                goto modrm_found;
        }
        /* then if not found, a register or indirection (shift instructions) */
        for(i = 0;i < nb_ops; i++) {
            if (op_type[i] & (OP_REG | OP_MMX | OP_SSE | OP_INDIR))
                goto modrm_found;
        }
#ifdef ASM_DEBUG
        tcc_error(-1, "bad op table");
#endif
    modrm_found:
        modrm_index = i;
        /* if a register is used in another operand then it is
           used instead of group */
        for(i = 0;i < nb_ops; i++) {
            int t = op_type[i];
            if (i != modrm_index &&
                (t & (OP_REG | OP_MMX | OP_SSE | OP_CR | OP_TR | OP_DB | OP_SEG))) {
                modreg_index = i;
                break;
            }
        }
    }
#ifdef TCC_TARGET_X86_64
    asm_rex (rex64, ops, nb_ops, op_type, modreg_index, modrm_index);
#endif

    if (pa->instr_type & OPC_REG) {
        /* mov $im, %reg case */
        if (v == 0xb0 && s >= 1)
            v += 7;
        for(i = 0; i < nb_ops; i++) {
            if (op_type[i] & (OP_REG | OP_ST)) {
                v += ops[i].reg;
                break;
            }
        }
    }
    if (pa->instr_type & OPC_B)
        v += s >= 1;
    if (nb_ops == 1 && pa->op_type[0] == OPT_DISP8) {
	ElfSym *esym;
        int jmp_disp;

        /* see if we can really generate the jump with a byte offset */
	esym = elfsym(ops[0].e.sym);
        if (!esym || esym->st_shndx != cur_text_section->sh_num)
            goto no_short_jump;
        jmp_disp = ops[0].e.v + esym->st_value - ind - 2 - (v >= 0xff);
        if (jmp_disp == (int8_t)jmp_disp) {
            /* OK to generate jump */
	    ops[0].e.sym = 0;
            ops[0].e.v = jmp_disp;
	    op_type[0] = OP_IM8S;
        } else {
        no_short_jump:
	    /* long jump will be allowed. need to modify the
	       opcode slightly */
	    if (v == 0xeb) /* jmp */
	        v = 0xe9;
	    else if (v == 0x70) /* jcc */
	        v += 0x0f10;
	    else  tcc_error(-1, "invalid displacement");
        }
    }
    if (OPCT_IS(pa->instr_type, OPC_TEST))
        v += test_bits[opcode - pa->sym];
    op1 = v >> 16;
    if (op1)
        g(op1);
    op1 = (v >> 8) & 0xff;
    if (op1)
        g(op1);
    g(v);

    if (OPCT_IS(pa->instr_type, OPC_SHIFT)) {
        reg = (opcode - pa->sym) / NBWLX;
        if (reg == 6)
            reg = 7;
    } else if (OPCT_IS(pa->instr_type, OPC_ARITH)) {
        reg = (opcode - pa->sym) / NBWLX;
    } else if (OPCT_IS(pa->instr_type, OPC_FARITH)) {
        reg = (opcode - pa->sym) / 6;
    } else {
        reg = (pa->instr_type >> OPC_GROUP_SHIFT) & 7;
    }

    pc = 0;
    if (pa->instr_type & OPC_MODRM) {
        /* if a register is used in another operand then it is
           used instead of group */
	if (modreg_index >= 0)
	    reg = ops[modreg_index].reg;
        pc = asm_modrm(reg, &ops[modrm_index]);
    }

    /* emit constants */
#ifndef TCC_TARGET_X86_64
    if (!(pa->instr_type & OPC_0F)
	&& (pa->opcode == 0x9a || pa->opcode == 0xea)) {
        /* ljmp or lcall kludge */
	gen_expr32(&ops[1].e);
        if( ops[0].e.sym )  tcc_error(-1, "cannot relocate");
        gen_le16(ops[0].e.v);
        return;
    }
#endif
    for(i = 0;i < nb_ops; i++) {
        v = op_type[i];
        if (v & (OP_IM8 | OP_IM16 | OP_IM32 | OP_IM64 | OP_IM8S | OP_ADDR)) {
            /* if multiple sizes are given it means we must look
               at the op size */
            if ((v | OP_IM8 | OP_IM64) == (OP_IM8 | OP_IM16 | OP_IM32 | OP_IM64)) {
                if (s == 0)
                    v = OP_IM8;
                else if (s == 1)
                    v = OP_IM16;
                else if (s == 2 || (v & OP_IM64) == 0)
                    v = OP_IM32;
                else
                    v = OP_IM64;
            }

            if(( v & ( OP_IM8 | OP_IM8S | OP_IM16 )) && ops[i].e.sym )  tcc_error(-1, "cannot relocate");

            if (v & (OP_IM8 | OP_IM8S)) {
                g(ops[i].e.v);
            } else if (v & OP_IM16) {
                gen_le16(ops[i].e.v);
#ifdef TCC_TARGET_X86_64
            } else if (v & OP_IM64) {
                gen_expr64(&ops[i].e);
#endif
	    } else if (pa->op_type[i] == OPT_DISP || pa->op_type[i] == OPT_DISP8) {
                gen_disp32(&ops[i].e);
            } else {
                gen_expr32(&ops[i].e);
            }
        }
    }

    /* after immediate operands, adjust pc-relative address */
    if (pc)
        add32le(cur_text_section->data + pc - 4, pc - ind);
}

/* return the constraint priority (we allocate first the lowest
   numbered constraints) */
static inline int constraint_priority(const char *str)
{
    int priority, c, pr;

    /* we take the lowest priority */
    priority = 0;
    for(;;) {
        c = *str;
        if (c == '\0')
            break;
        str++;
        switch(c) {
        case 'A':
            pr = 0;
            break;
        case 'a':
        case 'b':
        case 'c':
        case 'd':
        case 'S':
        case 'D':
            pr = 1;
            break;
        case 'q':
            pr = 2;
            break;
        case 'r':
	case 'R':
	case 'p':
            pr = 3;
            break;
        case 'N':
        case 'M':
        case 'I':
	case 'e':
        case 'i':
        case 'm':
        case 'g':
            pr = 4;
            break;
        default:
            tcc_error(-1, "unknown constraint '%c'", c);
            pr = 0;
        }
        if (pr > priority)
            priority = pr;
    }
    return priority;
}

static const char *skip_constraint_modifiers(const char *p)
{
    while (*p == '=' || *p == '&' || *p == '+' || *p == '%')
        p++;
    return p;
}

/* If T (a token) is of the form "%reg" returns the register
   number and type, otherwise return -1.  */
ST_FUNC int asm_parse_regvar (int t)
{
    const char *s;
    Operand op;
    if (t < TOK_IDENT)
        return -1;
    s = table_ident[t - TOK_IDENT]->str;
    if (s[0] != '%')
        return -1;
    t = tok_alloc(s+1, strlen(s)-1)->tok;
    unget_tok(t);
    unget_tok('%');
    parse_operand(tcc_state, &op);
    /* Accept only integer regs for now.  */
    if (op.type & OP_REG)
        return op.reg;
    else
        return -1;
}

#define REG_OUT_MASK 0x01
#define REG_IN_MASK  0x02

#define is_reg_allocated(reg) (regs_allocated[reg] & reg_mask)

ST_FUNC void asm_compute_constraints(ASMOperand *operands,
                                    int nb_operands, int nb_outputs,
                                    const uint8_t *clobber_regs,
                                    int *pout_reg)
{
    ASMOperand *op;
    int sorted_op[MAX_ASM_OPERANDS];
    int i, j, k, p1, p2, tmp, reg, c, reg_mask;
    const char *str;
    uint8_t regs_allocated[NB_ASM_REGS];

    /* init fields */
    for(i=0;i<nb_operands;i++) {
        op = &operands[i];
        op->input_index = -1;
        op->ref_index = -1;
        op->reg = -1;
        op->is_memory = 0;
        op->is_rw = 0;
    }
    /* compute constraint priority and evaluate references to output
       constraints if input constraints */
    for(i=0;i<nb_operands;i++) {
        op = &operands[i];
        str = op->constraint;
        str = skip_constraint_modifiers(str);
        if (isnum(*str) || *str == '[') {
            /* this is a reference to another constraint */
            k = find_constraint(operands, nb_operands, str, NULL);
            if ((unsigned)k >= i || i < nb_outputs)
                tcc_error(-1, "invalid reference in constraint %d ('%s')", i, str);
            op->ref_index = k;
            if (operands[k].input_index >= 0)
                tcc_error(-1, "cannot reference twice the same operand");
            operands[k].input_index = i;
            op->priority = 5;
	} else if ((op->vt->r & VT_VALMASK) == VT_LOCAL
		   && op->vt->sym
		   && (reg = op->vt->sym->r & VT_VALMASK) < VT_CONST) {
	    op->priority = 1;
	    op->reg = reg;
        } else {
            op->priority = constraint_priority(str);
        }
    }

    /* sort operands according to their priority */
    for(i=0;i<nb_operands;i++)
        sorted_op[i] = i;
    for(i=0;i<nb_operands - 1;i++) {
        for(j=i+1;j<nb_operands;j++) {
            p1 = operands[sorted_op[i]].priority;
            p2 = operands[sorted_op[j]].priority;
            if (p2 < p1) {
                tmp = sorted_op[i];
                sorted_op[i] = sorted_op[j];
                sorted_op[j] = tmp;
            }
        }
    }

    for(i = 0;i < NB_ASM_REGS; i++) {
        if (clobber_regs[i])
            regs_allocated[i] = REG_IN_MASK | REG_OUT_MASK;
        else
            regs_allocated[i] = 0;
    }
    /* esp cannot be used */
    regs_allocated[4] = REG_IN_MASK | REG_OUT_MASK;
    /* ebp cannot be used yet */
    regs_allocated[5] = REG_IN_MASK | REG_OUT_MASK;

    /* allocate registers and generate corresponding asm moves */
    for(i=0;i<nb_operands;i++) {
        j = sorted_op[i];
        op = &operands[j];
        str = op->constraint;
        /* no need to allocate references */
        if (op->ref_index >= 0)
            continue;
        /* select if register is used for output, input or both */
        if (op->input_index >= 0) {
            reg_mask = REG_IN_MASK | REG_OUT_MASK;
        } else if (j < nb_outputs) {
            reg_mask = REG_OUT_MASK;
        } else {
            reg_mask = REG_IN_MASK;
        }
	if (op->reg >= 0) {
	    if( is_reg_allocated( op->reg ))  tcc_error(-1, "asm regvar requests register that's taken already");
	    reg = op->reg;
	    goto reg_found;
	}
    try_next:
        c = *str++;
        switch(c) {
        case '=':
            goto try_next;
        case '+':
            op->is_rw = 1;
            /* FALL THRU */
        case '&':
            if( j >= nb_outputs )  tcc_error(-1, "'%c' modifier can only be applied to outputs", c);
            reg_mask = REG_IN_MASK | REG_OUT_MASK;
            goto try_next;
        case 'A':
            /* allocate both eax and edx */
            if (is_reg_allocated(TREG_XAX) ||
                is_reg_allocated(TREG_XDX))
                goto try_next;
            op->is_llong = 1;
            op->reg = TREG_XAX;
            regs_allocated[TREG_XAX] |= reg_mask;
            regs_allocated[TREG_XDX] |= reg_mask;
            break;
        case 'a':
            reg = TREG_XAX;
            goto alloc_reg;
        case 'b':
            reg = 3;
            goto alloc_reg;
        case 'c':
            reg = TREG_XCX;
            goto alloc_reg;
        case 'd':
            reg = TREG_XDX;
            goto alloc_reg;
        case 'S':
            reg = 6;
            goto alloc_reg;
        case 'D':
            reg = 7;
        alloc_reg:
            if (is_reg_allocated(reg))
                goto try_next;
            goto reg_found;
        case 'q':
            /* eax, ebx, ecx or edx */
            for(reg = 0; reg < 4; reg++) {
                if (!is_reg_allocated(reg))
                    goto reg_found;
            }
            goto try_next;
        case 'r':
	case 'R':
	case 'p': /* A general address, for x86(64) any register is acceptable*/
            /* any general register */
            for(reg = 0; reg < 8; reg++) {
                if (!is_reg_allocated(reg))
                    goto reg_found;
            }
            goto try_next;
        reg_found:
            /* now we can reload in the register */
            op->is_llong = 0;
            op->reg = reg;
            regs_allocated[reg] |= reg_mask;
            break;
	case 'e':
        case 'i':
            if (!((op->vt->r & (VT_VALMASK | VT_LVAL)) == VT_CONST))
                goto try_next;
            break;
        case 'I':
        case 'N':
        case 'M':
            if (!((op->vt->r & (VT_VALMASK | VT_LVAL | VT_SYM)) == VT_CONST))
                goto try_next;
            break;
        case 'm':
        case 'g':
            /* nothing special to do because the operand is already in
               memory, except if the pointer itself is stored in a
               memory variable (VT_LLOCAL case) */
            /* XXX: fix constant case */
            /* if it is a reference to a memory zone, it must lie
               in a register, so we reserve the register in the
               input registers and a load will be generated
               later */
            if (j < nb_outputs || c == 'm') {
                if ((op->vt->r & VT_VALMASK) == VT_LLOCAL) {
                    /* any general register */
                    for(reg = 0; reg < 8; reg++) {
                        if (!(regs_allocated[reg] & REG_IN_MASK))
                            goto reg_found1;
                    }
                    goto try_next;
                reg_found1:
                    /* now we can reload in the register */
                    regs_allocated[reg] |= REG_IN_MASK;
                    op->reg = reg;
                    op->is_memory = 1;
                }
            }
            break;
        default:
            tcc_error(-1, "asm constraint %d ('%s') could not be satisfied", j, op->constraint);
            break;
        }
        /* if a reference is present for that operand, we assign it too */
        if (op->input_index >= 0) {
            operands[op->input_index].reg = op->reg;
            operands[op->input_index].is_llong = op->is_llong;
        }
    }

    /* compute out_reg. It is used to store outputs registers to memory
       locations references by pointers (VT_LLOCAL case) */
    *pout_reg = -1;
    for(i=0;i<nb_operands;i++) {
        op = &operands[i];
        if (op->reg >= 0 &&
            (op->vt->r & VT_VALMASK) == VT_LLOCAL  &&
            !op->is_memory) {
            for(reg = 0; reg < 8; reg++) {
                if (!(regs_allocated[reg] & REG_OUT_MASK))
                    goto reg_found2;
            }
            tcc_error(-1, "could not find free output register for reloading");
        reg_found2:
            *pout_reg = reg;
            break;
        }
    }

    /* print sorted constraints */
#ifdef ASM_DEBUG
    for(i=0;i<nb_operands;i++) {
        j = sorted_op[i];
        op = &operands[j];
        printf("%%%d [%s]: \"%s\" r=0x%04x reg=%d\n",
               j,
               op->id ? get_tok_str(op->id, NULL) : "",
               op->constraint,
               op->vt->r,
               op->reg);
    }
    if (*pout_reg >= 0)
        printf("out_reg=%d\n", *pout_reg);
#endif
}

ST_FUNC void subst_asm_operand(CString *add_str,
                              SValue *sv, int modifier)
{
    int r, reg, size, val;
    char buf[64];

    r = sv->r;
    if ((r & VT_VALMASK) == VT_CONST) {
        if (!(r & VT_LVAL) && modifier != 'c' && modifier != 'n' &&
	    modifier != 'P')
            cstr_ccat(add_str, '$');
        if (r & VT_SYM) {
	    const char *name = get_tok_str(sv->sym->v, NULL);
	    if (sv->sym->v >= SYM_FIRST_ANOM) {
		/* In case of anonymous symbols ("L.42", used
		   for static data labels) we can't find them
		   in the C symbol table when later looking up
		   this name.  So enter them now into the asm label
		   list when we still know the symbol.  */
		get_asm_sym(tok_alloc(name, strlen(name))->tok, sv->sym);
	    }
            cstr_cat(add_str, name, -1);
            if ((uint32_t)sv->c.i == 0)
                goto no_offset;
	    cstr_ccat(add_str, '+');
        }
        val = sv->c.i;
        if (modifier == 'n')
            val = -val;
        snprintf(buf, sizeof(buf), "%d", (int)sv->c.i);
        cstr_cat(add_str, buf, -1);
    no_offset:;
#ifdef TCC_TARGET_X86_64
        if (r & VT_LVAL)
            cstr_cat(add_str, "(%rip)", -1);
#endif
    } else if ((r & VT_VALMASK) == VT_LOCAL) {
#ifdef TCC_TARGET_X86_64
        snprintf(buf, sizeof(buf), "%d(%%rbp)", (int)sv->c.i);
#else
        snprintf(buf, sizeof(buf), "%d(%%ebp)", (int)sv->c.i);
#endif
        cstr_cat(add_str, buf, -1);
    } else if (r & VT_LVAL) {
        reg = r & VT_VALMASK;
        if( reg >= VT_CONST )  tcc_error(-1, "internal compiler error");
        snprintf(buf, sizeof(buf), "(%%%s)",
#ifdef TCC_TARGET_X86_64
                 get_tok_str(TOK_ASM_rax + reg, NULL)
#else
                 get_tok_str(TOK_ASM_eax + reg, NULL)
#endif
		 );
        cstr_cat(add_str, buf, -1);
    } else {
        /* register case */
        reg = r & VT_VALMASK;
        if( reg >= VT_CONST )  tcc_error(-1, "internal compiler error");

        /* choose register operand size */
        if ((sv->type.t & VT_BTYPE) == VT_BYTE ||
	    (sv->type.t & VT_BTYPE) == VT_BOOL)
            size = 1;
        else if ((sv->type.t & VT_BTYPE) == VT_SHORT)
            size = 2;
#ifdef TCC_TARGET_X86_64
        else if ((sv->type.t & VT_BTYPE) == VT_LLONG ||
		 (sv->type.t & VT_BTYPE) == VT_PTR)
            size = 8;
#endif
        else
            size = 4;
        if (size == 1 && reg >= 4)
            size = 4;

        if (modifier == 'b') {
            if( reg >= 4 )  tcc_error(-1, "cannot use byte register");
            size = 1;
        } else if (modifier == 'h') {
            if( reg >= 4 )  tcc_error(-1, "cannot use byte register");
            size = -1;
        } else if (modifier == 'w') {
            size = 2;
        } else if (modifier == 'k') {
            size = 4;
#ifdef TCC_TARGET_X86_64
        } else if (modifier == 'q') {
            size = 8;
#endif
        }

        switch(size) {
        case -1:
            reg = TOK_ASM_ah + reg;
            break;
        case 1:
            reg = TOK_ASM_al + reg;
            break;
        case 2:
            reg = TOK_ASM_ax + reg;
            break;
        default:
            reg = TOK_ASM_eax + reg;
            break;
#ifdef TCC_TARGET_X86_64
        case 8:
            reg = TOK_ASM_rax + reg;
            break;
#endif
        }
        snprintf(buf, sizeof(buf), "%%%s", get_tok_str(reg, NULL));
        cstr_cat(add_str, buf, -1);
    }
}

/* generate prolog and epilog code for asm statement */
ST_FUNC void asm_gen_code(ASMOperand *operands, int nb_operands,
                         int nb_outputs, int is_output,
                         uint8_t *clobber_regs,
                         int out_reg)
{
    uint8_t regs_allocated[NB_ASM_REGS];
    ASMOperand *op;
    int i, reg;

    /* Strictly speaking %Xbp and %Xsp should be included in the
       call-preserved registers, but currently it doesn't matter.  */
#ifdef TCC_TARGET_X86_64
#ifdef TCC_TARGET_PE
    static uint8_t reg_saved[] = { 3, 6, 7, 12, 13, 14, 15 };
#else
    static uint8_t reg_saved[] = { 3, 12, 13, 14, 15 };
#endif
#else
    static uint8_t reg_saved[] = { 3, 6, 7 };
#endif

    /* mark all used registers */
    memcpy(regs_allocated, clobber_regs, sizeof(regs_allocated));
    for(i = 0; i < nb_operands;i++) {
        op = &operands[i];
        if (op->reg >= 0)
            regs_allocated[op->reg] = 1;
    }
    if (!is_output) {
        /* generate reg save code */
        for(i = 0; i < sizeof(reg_saved)/sizeof(reg_saved[0]); i++) {
            reg = reg_saved[i];
            if (regs_allocated[reg]) {
		if (reg >= 8)
		  g(0x41), reg-=8;
                g(0x50 + reg);
            }
        }

        /* generate load code */
        for(i = 0; i < nb_operands; i++) {
            op = &operands[i];
            if (op->reg >= 0) {
                if ((op->vt->r & VT_VALMASK) == VT_LLOCAL &&
                    op->is_memory) {
                    /* memory reference case (for both input and
                       output cases) */
                    SValue sv;
                    sv = *op->vt;
                    sv.r = (sv.r & ~VT_VALMASK) | VT_LOCAL | VT_LVAL;
                    sv.type.t = VT_PTR;
                    load(op->reg, &sv);
                } else if (i >= nb_outputs || op->is_rw) {
                    /* load value in register */
                    load(op->reg, op->vt);
                    if (op->is_llong) {
                        SValue sv;
                        sv = *op->vt;
                        sv.c.i += 4;
                        load(TREG_XDX, &sv);
                    }
                }
            }
        }
    } else {
        /* generate save code */
        for(i = 0 ; i < nb_outputs; i++) {
            op = &operands[i];
            if (op->reg >= 0) {
                if ((op->vt->r & VT_VALMASK) == VT_LLOCAL) {
                    if (!op->is_memory) {
                        SValue sv;
                        sv = *op->vt;
                        sv.r = (sv.r & ~VT_VALMASK) | VT_LOCAL;
			sv.type.t = VT_PTR;
                        load(out_reg, &sv);

			sv = *op->vt;
                        sv.r = (sv.r & ~VT_VALMASK) | out_reg;
                        store(op->reg, &sv);
                    }
                } else {
                    store(op->reg, op->vt);
                    if (op->is_llong) {
                        SValue sv;
                        sv = *op->vt;
                        sv.c.i += 4;
                        store(TREG_XDX, &sv);
                    }
                }
            }
        }
        /* generate reg restore code */
        for(i = sizeof(reg_saved)/sizeof(reg_saved[0]) - 1; i >= 0; i--) {
            reg = reg_saved[i];
            if (regs_allocated[reg]) {
		if (reg >= 8)
		  g(0x41), reg-=8;
                g(0x58 + reg);
            }
        }
    }
}

ST_FUNC void asm_clobber(uint8_t *clobber_regs, const char *str)
{
    int reg;
    TokenSym *ts;
#ifdef TCC_TARGET_X86_64
    unsigned int type;
#endif

    if (!strcmp(str, "memory") ||
        !strcmp(str, "cc") ||
	!strcmp(str, "flags"))
        return;
    ts = tok_alloc(str, strlen(str));
    reg = ts->tok;
    if (reg >= TOK_ASM_eax && reg <= TOK_ASM_edi) {
        reg -= TOK_ASM_eax;
    } else if (reg >= TOK_ASM_ax && reg <= TOK_ASM_di) {
        reg -= TOK_ASM_ax;
#ifdef TCC_TARGET_X86_64
    } else if (reg >= TOK_ASM_rax && reg <= TOK_ASM_rdi) {
        reg -= TOK_ASM_rax;
    } else if ((reg = asm_parse_numeric_reg(reg, &type)) >= 0) {
	;
#endif
    }
    else  tcc_error(-1, "invalid clobber register '%s'", str);
    clobber_regs[reg] = 1;
}

#endif

#ifdef CONFIG_TCC_ASM

/*  GAS like assembler for TCC
 *  Copyright (c) 2001-2004 Fabrice Bellard
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */

#ifdef CONFIG_TCC_ASM

ST_FUNC int asm_get_local_label_name(TCCState *s1, unsigned int n)
{
    char buf[64];
    TokenSym *ts;

    snprintf(buf, sizeof(buf), "L..%u", n);
    ts = tok_alloc(buf, strlen(buf));
    return ts->tok;
}

static int tcc_assemble_internal(TCCState *s1, int do_preprocess, int global);
static Sym* asm_new_label(TCCState *s1, int label, int is_local);
static Sym* asm_new_label1(TCCState *s1, int label, int is_local, int sh_num, int value);

static Sym *asm_label_find(int v)
{
    Sym *sym = sym_find(v);
    while (sym && sym->sym_scope)
        sym = sym->prev_tok;
    return sym;
}

static Sym *asm_label_push(int v)
{
    /* We always add VT_EXTERN, for sym definition that's tentative
       (for .set, removed for real defs), for mere references it's correct
       as is.  */
    Sym *sym = global_identifier_push(v, VT_ASM | VT_EXTERN | VT_STATIC, 0);
    sym->r = VT_CONST | VT_SYM;
    return sym;
}

/* Return a symbol we can use inside the assembler, having name NAME.
   Symbols from asm and C source share a namespace.  If we generate
   an asm symbol it's also a (file-global) C symbol, but it's
   either not accessible by name (like "L.123"), or its type information
   is such that it's not usable without a proper C declaration.

   Sometimes we need symbols accessible by name from asm, which
   are anonymous in C, in this case CSYM can be used to transfer
   all information from that symbol to the (possibly newly created)
   asm symbol.  */
ST_FUNC Sym* get_asm_sym(int name, Sym *csym)
{
    Sym *sym = asm_label_find(name);
    if (!sym) {
	sym = asm_label_push(name);
	if (csym)
	  sym->c = csym->c;
    }
    return sym;
}

static Sym* asm_section_sym(TCCState *s1, Section *sec)
{
    char buf[100];
    int label = tok_alloc(buf,
        snprintf(buf, sizeof buf, "L.%s", sec->name)
        )->tok;
    Sym *sym = asm_label_find(label);
    return sym ? sym : asm_new_label1(s1, label, 1, sec->sh_num, 0);
}

/* We do not use the C expression parser to handle symbols. Maybe the
   C expression parser could be tweaked to do so. */

static void asm_expr_unary(TCCState *s1, ExprValue *pe)
{
    Sym *sym;
    int op, label;
    uint64_t n;
    const char *p;

    switch(tok) {
    case TOK_PPNUM:
        p = tokc.str.data;
        n = strtoull(p, (char **)&p, 0);
        if (*p == 'b' || *p == 'f') {
            /* backward or forward label */
            label = asm_get_local_label_name(s1, n);
            sym = asm_label_find(label);
            if (*p == 'b') {
                /* backward : find the last corresponding defined label */
                if (sym && (!sym->c || elfsym(sym)->st_shndx == SHN_UNDEF))
                    sym = sym->prev_tok;
                if( !sym )  tcc_error(-1, "local label '%d' not found backward", n);
            }
            else {
                /* forward */
                if (!sym || (sym->c && elfsym(sym)->st_shndx != SHN_UNDEF)) {
                    /* if the last label is defined, then define a new one */
		    sym = asm_label_push(label);
                }
            }
	    pe->v = 0;
	    pe->sym = sym;
	    pe->pcrel = 0;
        } else if (*p == '\0') {
            pe->v = n;
            pe->sym = NULL;
	    pe->pcrel = 0;
        }
        else  tcc_error(-1, "invalid number syntax");
        next();
        break;
    case '+':
        next();
        asm_expr_unary(s1, pe);
        break;
    case '-':
    case '~':
        op = tok;
        next();
        asm_expr_unary(s1, pe);
        if( pe->sym )  tcc_error(-1, "invalid operation with label");
        if (op == '-')
            pe->v = -pe->v;
        else
            pe->v = ~pe->v;
        break;
    case TOK_CCHAR:
    case TOK_LCHAR:
	pe->v = tokc.i;
	pe->sym = NULL;
	pe->pcrel = 0;
	next();
	break;
    case '(':
        next();
        asm_expr(s1, pe);
        skip(')');
        break;
    case '.':
        pe->v = ind;
        pe->sym = asm_section_sym(s1, cur_text_section);
        pe->pcrel = 0;
        next();
        break;
    default:
        if (tok >= TOK_IDENT) {
	    ElfSym *esym;
            /* label case : if the label was not found, add one */
	    sym = get_asm_sym(tok, NULL);
	    esym = elfsym(sym);
            if (esym && esym->st_shndx == SHN_ABS) {
                /* if absolute symbol, no need to put a symbol value */
                pe->v = esym->st_value;
                pe->sym = NULL;
		pe->pcrel = 0;
            } else {
                pe->v = 0;
                pe->sym = sym;
		pe->pcrel = 0;
            }
            next();
        }
        else  tcc_error(-1, "bad expression syntax [%s]", get_tok_str(tok, &tokc));
        break;
    }
}
    
static void asm_expr_prod(TCCState *s1, ExprValue *pe)
{
    int op;
    ExprValue e2;

    asm_expr_unary(s1, pe);
    for(;;) {
        op = tok;
        if (op != '*' && op != '/' && op != '%' && 
            op != TOK_SHL && op != TOK_SAR)
            break;
        next();
        asm_expr_unary(s1, &e2);
        if( pe->sym || e2.sym )  tcc_error(-1, "invalid operation with label");
        switch(op) {
        case '*':
            pe->v *= e2.v;
            break;
        case '/':  
            if (e2.v == 0) {
            div_error:
                tcc_error(-1, "division by zero");
            }
            pe->v /= e2.v;
            break;
        case '%':  
            if (e2.v == 0)
                goto div_error;
            pe->v %= e2.v;
            break;
        case TOK_SHL:
            pe->v <<= e2.v;
            break;
        default:
        case TOK_SAR:
            pe->v >>= e2.v;
            break;
        }
    }
}

static void asm_expr_logic(TCCState *s1, ExprValue *pe)
{
    int op;
    ExprValue e2;

    asm_expr_prod(s1, pe);
    for(;;) {
        op = tok;
        if (op != '&' && op != '|' && op != '^')
            break;
        next();
        asm_expr_prod(s1, &e2);
        if( pe->sym || e2.sym )  tcc_error(-1, "invalid operation with label");
        switch(op) {
        case '&':
            pe->v &= e2.v;
            break;
        case '|':  
            pe->v |= e2.v;
            break;
        default:
        case '^':
            pe->v ^= e2.v;
            break;
        }
    }
}

static inline void asm_expr_sum(TCCState *s1, ExprValue *pe)
{
    int op;
    ExprValue e2;

    asm_expr_logic(s1, pe);
    for(;;) {
        op = tok;
        if (op != '+' && op != '-')
            break;
        next();
        asm_expr_logic(s1, &e2);
        if (op == '+') {
            if (pe->sym != NULL && e2.sym != NULL)
                goto cannot_relocate;
            pe->v += e2.v;
            if (pe->sym == NULL && e2.sym != NULL)
                pe->sym = e2.sym;
        } else {
            pe->v -= e2.v;
            /* NOTE: we are less powerful than gas in that case
               because we store only one symbol in the expression */
	    if (!e2.sym) {
		/* OK */
	    } else if (pe->sym == e2.sym) { 
		/* OK */
		pe->sym = NULL; /* same symbols can be subtracted to NULL */
	    } else {
		ElfSym *esym1, *esym2;
		esym1 = elfsym(pe->sym);
		esym2 = elfsym(e2.sym);
		if (esym1 && esym1->st_shndx == esym2->st_shndx
		    && esym1->st_shndx != SHN_UNDEF) {
		    /* we also accept defined symbols in the same section */
		    pe->v += esym1->st_value - esym2->st_value;
		    pe->sym = NULL;
		} else if (esym2->st_shndx == cur_text_section->sh_num) {
		    /* When subtracting a defined symbol in current section
		       this actually makes the value PC-relative.  */
		    pe->v -= esym2->st_value - ind - 4;
		    pe->pcrel = 1;
		    e2.sym = NULL;
		} else {
cannot_relocate:
		    tcc_error(-1, "invalid operation with label");
		}
	    }
        }
    }
}

static inline void asm_expr_cmp(TCCState *s1, ExprValue *pe)
{
    int op;
    ExprValue e2;

    asm_expr_sum(s1, pe);
    for(;;) {
        op = tok;
	if (op != TOK_EQ && op != TOK_NE
	    && (op > TOK_GT || op < TOK_ULE))
            break;
        next();
        asm_expr_sum(s1, &e2);
        if( pe->sym || e2.sym )  tcc_error(-1, "invalid operation with label");
        switch(op) {
	case TOK_EQ:
	    pe->v = pe->v == e2.v;
	    break;
	case TOK_NE:
	    pe->v = pe->v != e2.v;
	    break;
	case TOK_LT:
	    pe->v = (int64_t)pe->v < (int64_t)e2.v;
	    break;
	case TOK_GE:
	    pe->v = (int64_t)pe->v >= (int64_t)e2.v;
	    break;
	case TOK_LE:
	    pe->v = (int64_t)pe->v <= (int64_t)e2.v;
	    break;
	case TOK_GT:
	    pe->v = (int64_t)pe->v > (int64_t)e2.v;
	    break;
        default:
            break;
        }
	/* GAS compare results are -1/0 not 1/0.  */
	pe->v = -(int64_t)pe->v;
    }
}

ST_FUNC void asm_expr(TCCState *s1, ExprValue *pe)
{
    asm_expr_cmp(s1, pe);
}

ST_FUNC int asm_int_expr(TCCState *s1)
{
    ExprValue e;
    asm_expr(s1, &e);
    if( e.sym )  tcc_error(-1, "constant expected" );
    return e.v;
}

static Sym* asm_new_label1(TCCState *s1, int label, int is_local,
                           int sh_num, int value)
{
    Sym *sym;
    ElfSym *esym;

    sym = asm_label_find(label);
    if (sym) {
	esym = elfsym(sym);
	/* A VT_EXTERN symbol, even if it has a section is considered
	   overridable.  This is how we "define" .set targets.  Real
	   definitions won't have VT_EXTERN set.  */
        if (esym && esym->st_shndx != SHN_UNDEF) {
            /* the label is already defined */
            if (IS_ASM_SYM(sym)
                && (is_local == 1 || (sym->type.t & VT_EXTERN)))
                goto new_label;
            if (!(sym->type.t & VT_EXTERN))
                tcc_error(-1, "assembler label '%s' already defined",
                          get_tok_str(label, NULL));
        }
    } else {
    new_label:
        sym = asm_label_push(label);
    }
    if (!sym->c)
      put_extern_sym2(sym, SHN_UNDEF, 0, 0, 0);
    esym = elfsym(sym);
    esym->st_shndx = sh_num;
    esym->st_value = value;
    if (is_local != 2)
        sym->type.t &= ~VT_EXTERN;
    return sym;
}

static Sym* asm_new_label(TCCState *s1, int label, int is_local)
{
    return asm_new_label1(s1, label, is_local, cur_text_section->sh_num, ind);
}

/* Set the value of LABEL to that of some expression (possibly
   involving other symbols).  LABEL can be overwritten later still.  */
static Sym* set_symbol(TCCState *s1, int label)
{
    long n;
    ExprValue e;
    Sym *sym;
    ElfSym *esym;
    next();
    asm_expr(s1, &e);
    n = e.v;
    esym = elfsym(e.sym);
    if (esym)
	n += esym->st_value;
    sym = asm_new_label1(s1, label, 2, esym ? esym->st_shndx : SHN_ABS, n);
    elfsym(sym)->st_other |= ST_ASM_SET;
    return sym;
}

static void use_section1(TCCState *s1, Section *sec)
{
    cur_text_section->data_offset = ind;
    cur_text_section = sec;
    ind = cur_text_section->data_offset;
}

static void use_section(TCCState *s1, const char *name)
{
    Section *sec;
    sec = find_section(s1, name);
    use_section1(s1, sec);
}

static void push_section(TCCState *s1, const char *name)
{
    Section *sec = find_section(s1, name);
    sec->prev = cur_text_section;
    use_section1(s1, sec);
}

static void pop_section(TCCState *s1)
{
    Section *prev = cur_text_section->prev;
    if( !prev )  tcc_error(-1, ".popsection without .pushsection");
    cur_text_section->prev = NULL;
    use_section1(s1, prev);
}

static void asm_parse_directive(TCCState *s1, int global)
{
    int n, offset, v, size, tok1;
    Section *sec;
    uint8_t *ptr;

    /* assembler directive */
    sec = cur_text_section;
    switch(tok) {
    case TOK_ASMDIR_align:
    case TOK_ASMDIR_balign:
    case TOK_ASMDIR_p2align:
    case TOK_ASMDIR_skip:
    case TOK_ASMDIR_space:
        tok1 = tok;
        next();
        n = asm_int_expr(s1);
        if (tok1 == TOK_ASMDIR_p2align)
        {
            if (n < 0 || n > 30)
                tcc_error(-1, "invalid p2align, must be between 0 and 30");
            n = 1 << n;
            tok1 = TOK_ASMDIR_align;
        }
        if (tok1 == TOK_ASMDIR_align || tok1 == TOK_ASMDIR_balign) {
            if (n < 0 || (n & (n-1)) != 0)
                tcc_error(-1, "alignment must be a positive power of two");
            offset = (ind + n - 1) & -n;
            size = offset - ind;
            /* the section must have a compatible alignment */
            if (sec->sh_addralign < n)
                sec->sh_addralign = n;
        } else {
	    if (n < 0)
	        n = 0;
            size = n;
        }
        v = 0;
        if (tok == ',') {
            next();
            v = asm_int_expr(s1);
        }
    zero_pad:
        if (sec->sh_type != SHT_NOBITS) {
            sec->data_offset = ind;
            ptr = section_ptr_add(sec, size);
            memset(ptr, v, size);
        }
        ind += size;
        break;
    case TOK_ASMDIR_quad:
#ifdef TCC_TARGET_X86_64
	size = 8;
	goto asm_data;
#else
        next();
        for(;;) {
            uint64_t vl;
            const char *p;

            p = tokc.str.data;
            if (tok != TOK_PPNUM) {
            error_constant:
                tcc_error(-1, "64 bit constant");
            }
            vl = strtoll(p, (char **)&p, 0);
            if (*p != '\0')
                goto error_constant;
            next();
            if (sec->sh_type != SHT_NOBITS) {
                /* XXX: endianness */
                gen_le32(vl);
                gen_le32(vl >> 32);
            } else {
                ind += 8;
            }
            if (tok != ',')
                break;
            next();
        }
        break;
#endif
    case TOK_ASMDIR_byte:
        size = 1;
        goto asm_data;
    case TOK_ASMDIR_word:
    case TOK_ASMDIR_short:
        size = 2;
        goto asm_data;
    case TOK_ASMDIR_long:
    case TOK_ASMDIR_int:
        size = 4;
    asm_data:
        next();
        for(;;) {
            ExprValue e;
            asm_expr(s1, &e);
            if (sec->sh_type != SHT_NOBITS) {
                if (size == 4) {
                    gen_expr32(&e);
#ifdef TCC_TARGET_X86_64
		} else if (size == 8) {
		    gen_expr64(&e);
#endif
                } else {
                    if( e.sym )  tcc_error(-1, "constant expected" );
                    if( size == 1 )  g(e.v);
                    else  gen_le16(e.v);
                }
            } else {
                ind += size;
            }
            if (tok != ',')
                break;
            next();
        }
        break;
    case TOK_ASMDIR_fill:
        {
            int repeat, size, val, i, j;
            uint8_t repeat_buf[8];
            next();
            repeat = asm_int_expr(s1);
            if (repeat < 0) {
                tcc_error(-1, "repeat < 0; .fill ignored");
                break;
            }
            size = 1;
            val = 0;
            if (tok == ',') {
                next();
                size = asm_int_expr(s1);
                if (size < 0) {
                    tcc_error(-1, "size < 0; .fill ignored");
                    break;
                }
                if (size > 8)
                    size = 8;
                if (tok == ',') {
                    next();
                    val = asm_int_expr(s1);
                }
            }
            /* XXX: endianness */
            repeat_buf[0] = val;
            repeat_buf[1] = val >> 8;
            repeat_buf[2] = val >> 16;
            repeat_buf[3] = val >> 24;
            repeat_buf[4] = 0;
            repeat_buf[5] = 0;
            repeat_buf[6] = 0;
            repeat_buf[7] = 0;
            for(i = 0; i < repeat; i++) {
                for(j = 0; j < size; j++) {
                    g(repeat_buf[j]);
                }
            }
        }
        break;
    case TOK_ASMDIR_rept:
        {
            int repeat;
            TokenString *init_str;
            next();
            repeat = asm_int_expr(s1);
            init_str = tok_str_alloc();
            while (next(), tok != TOK_ASMDIR_endr) {
                if (tok == CH_EOF)  tcc_error(-1, "we at end of file, .endr not found");
                tok_str_add_tok(init_str);
            }
            tok_str_add(init_str, -1);
            tok_str_add(init_str, 0);
            begin_macro(init_str, 1);
            while (repeat-- > 0) {
                tcc_assemble_internal(s1, (parse_flags & PARSE_FLAG_PREPROCESS), global);
                macro_ptr = init_str->str;
            }
            end_macro();
            next();
            break;
        }
    case TOK_ASMDIR_org:
        {
            unsigned long n;
	    ExprValue e;
	    ElfSym *esym;
            next();
	    asm_expr(s1, &e);
	    n = e.v;
	    esym = elfsym(e.sym);
	    if( esym ) {
		if( esym->st_shndx != cur_text_section->sh_num )  tcc_error(-1, "constant or same-section symbol expected" );
		n += esym->st_value;
	    }
            if( n < ind )  tcc_error(-1, "attempt to .org backwards");
            v = 0;
            size = n - ind;
            goto zero_pad;
        }
        break;
    case TOK_ASMDIR_set:
	next();
	tok1 = tok;
	next();
	/* Also accept '.set stuff', but don't do anything with this.
	   It's used in GAS to set various features like '.set mips16'.  */
	if (tok == ',')
	    set_symbol(s1, tok1);
	break;
    case TOK_ASMDIR_globl:
    case TOK_ASMDIR_global:
    case TOK_ASMDIR_weak:
    case TOK_ASMDIR_hidden:
	tok1 = tok;
	do { 
            Sym *sym;
            next();
            sym = get_asm_sym(tok, NULL);
	    if (tok1 != TOK_ASMDIR_hidden)
                sym->type.t &= ~VT_STATIC;
            if (tok1 == TOK_ASMDIR_weak)
                sym->a.weak = 1;
	    else if (tok1 == TOK_ASMDIR_hidden)
	        sym->a.visibility = STV_HIDDEN;
            update_storage(sym);
            next();
	} while (tok == ',');
	break;
    case TOK_ASMDIR_string:
    case TOK_ASMDIR_ascii:
    case TOK_ASMDIR_asciz:
        {
            const uint8_t *p;
            int i, size, t;

            t = tok;
            next();
            for(;;) {
                if( tok != TOK_STR )  tcc_error(-1, "string constant expected" );
                p = tokc.str.data;
                size = tokc.str.size;
                if (t == TOK_ASMDIR_ascii && size > 0)
                    size--;
                for(i = 0; i < size; i++)
                    g(p[i]);
                next();
                if (tok == ',') {
                    next();
                } else if (tok != TOK_STR) {
                    break;
                }
            }
	}
	break;
    case TOK_ASMDIR_text:
    case TOK_ASMDIR_data:
    case TOK_ASMDIR_bss:
	{ 
            char sname[64];
            tok1 = tok;
            n = 0;
            next();
            if (tok != ';' && tok != TOK_LINEFEED) {
		n = asm_int_expr(s1);
		next();
            }
            if (n)
                sprintf(sname, "%s%d", get_tok_str(tok1, NULL), n);
            else
                sprintf(sname, "%s", get_tok_str(tok1, NULL));
            use_section(s1, sname);
	}
	break;
    case TOK_ASMDIR_file:
        {
            char filename[512];

            filename[0] = '\0';
            next();

            if( tok == TOK_STR )  pstrcat(filename, sizeof(filename), tokc.str.data);
            else  pstrcat(filename, sizeof(filename), get_tok_str(tok, NULL));

            if( s1->warn_unsupported )  tcc_error(0, "ignoring .file %s", filename );

            next();
        }
        break;
    case TOK_ASMDIR_ident:
        {
            char ident[256];

            ident[0] = '\0';
            next();

            if (tok == TOK_STR)
                pstrcat(ident, sizeof(ident), tokc.str.data);
            else
                pstrcat(ident, sizeof(ident), get_tok_str(tok, NULL));

            if( s1->warn_unsupported )  tcc_error(0, "ignoring .ident %s", ident);

            next();
        }
        break;
    case TOK_ASMDIR_size:
        { 
            Sym *sym;

            next();
            sym = asm_label_find(tok);
            if (!sym) {
                tcc_error(-1, "label not found: %s", get_tok_str(tok, NULL));
            }

            /* XXX .size name,label2-label1 */
            if( s1->warn_unsupported )  tcc_error(0, "ignoring .size %s,*", get_tok_str(tok, NULL));

            next();
            skip(',');
            while (tok != TOK_LINEFEED && tok != ';' && tok != CH_EOF) {
                next();
            }
        }
        break;
    case TOK_ASMDIR_type:
        { 
            Sym *sym;
            const char *newtype;

            next();
            sym = get_asm_sym(tok, NULL);
            next();
            skip(',');
            if (tok == TOK_STR) {
                newtype = tokc.str.data;
            } else {
                if (tok == '@' || tok == '%')
                    next();
                newtype = get_tok_str(tok, NULL);
            }

            if (!strcmp(newtype, "function") || !strcmp(newtype, "STT_FUNC")) {
                sym->type.t = (sym->type.t & ~VT_BTYPE) | VT_FUNC;
            }
            else if (s1->warn_unsupported)
                tcc_error(0, "change type of '%s' from 0x%x to '%s' ignored", 
                    get_tok_str(sym->v, NULL), sym->type.t, newtype);

            next();
        }
        break;
    case TOK_ASMDIR_pushsection:
    case TOK_ASMDIR_section:
        {
            char sname[256];
	    int old_nb_section = s1->nb_sections;

	    tok1 = tok;
            /* XXX: support more options */
            next();
            sname[0] = '\0';
            while (tok != ';' && tok != TOK_LINEFEED && tok != ',') {
                if (tok == TOK_STR)
                    pstrcat(sname, sizeof(sname), tokc.str.data);
                else
                    pstrcat(sname, sizeof(sname), get_tok_str(tok, NULL));
                next();
            }
            if (tok == ',') {
                /* skip section options */
                next();
                if( tok != TOK_STR )  tcc_error(-1, "string constant expected" );
                next();
                if (tok == ',') {
                    next();
                    if (tok == '@' || tok == '%')
                        next();
                    next();
                }
            }
            last_text_section = cur_text_section;
	    if (tok1 == TOK_ASMDIR_section)
	        use_section(s1, sname);
	    else
	        push_section(s1, sname);
	    /* If we just allocated a new section reset its alignment to
	       1.  new_section normally acts for GCC compatibility and
	       sets alignment to PTR_SIZE.  The assembler behaves different. */
	    if (old_nb_section != s1->nb_sections)
	        cur_text_section->sh_addralign = 1;
        }
        break;
    case TOK_ASMDIR_previous:
        { 
            Section *sec;
            next();
            if( !last_text_section )  tcc_error(-1, "no previous section referenced");
            sec = cur_text_section;
            use_section1(s1, last_text_section);
            last_text_section = sec;
        }
        break;
    case TOK_ASMDIR_popsection:
	next();
	pop_section(s1);
	break;
#ifdef TCC_TARGET_I386
    case TOK_ASMDIR_code16:
        {
            next();
            s1->seg_size = 16;
        }
        break;
    case TOK_ASMDIR_code32:
        {
            next();
            s1->seg_size = 32;
        }
        break;
#endif
#ifdef TCC_TARGET_X86_64
    /* added for compatibility with GAS */
    case TOK_ASMDIR_code64:
        next();
        break;
#endif
    default:
        tcc_error(-1, "unknown assembler directive '.%s'", get_tok_str(tok, NULL));
        break;
    }
}


/* assemble a file */
static int tcc_assemble_internal(TCCState *s1, int do_preprocess, int global)
{
    int opcode;
    int saved_parse_flags = parse_flags;

    parse_flags = PARSE_FLAG_ASM_FILE | PARSE_FLAG_TOK_STR;
    if (do_preprocess)
        parse_flags |= PARSE_FLAG_PREPROCESS;
    for(;;) {
        next();
        if (tok == TOK_EOF)
            break;
#if defined CONFIG_TCC_GDEBUG
        /* generate line number info */
        if( global && s1->do_debug )  tcc_debug_line(s1);
#endif
        parse_flags |= PARSE_FLAG_LINEFEED; /* XXX: suppress that hack */
    redo:
        if (tok == '#') {
            /* horrible gas comment */
            while (tok != TOK_LINEFEED)
                next();
        } else if (tok >= TOK_ASMDIR_FIRST && tok <= TOK_ASMDIR_LAST) {
            asm_parse_directive(s1, global);
        } else if (tok == TOK_PPNUM) {
            const char *p;
            int n;
            p = tokc.str.data;
            n = strtoul(p, (char **)&p, 10);
            if( *p != '\0' )  tcc_error(-1, "':' expected" );
            /* new local label */
            asm_new_label(s1, asm_get_local_label_name(s1, n), 1);
            next();
            skip(':');
            goto redo;
        } else if (tok >= TOK_IDENT) {
            /* instruction or label */
            opcode = tok;
            next();
            if (tok == ':') {
                /* new label */
                asm_new_label(s1, opcode, 0);
                next();
                goto redo;
            } else if (tok == '=') {
		set_symbol(s1, opcode);
                goto redo;
            } else {
                asm_opcode(s1, opcode);
            }
        }
        /* end of line */
        if( tok != ';' && tok != TOK_LINEFEED )  tcc_error(-1, "end of line expected" );
        parse_flags &= ~PARSE_FLAG_LINEFEED; /* XXX: suppress that hack */
    }

    parse_flags = saved_parse_flags;
    return 0;
}

/* Assemble the current file */
ST_FUNC int tcc_assemble(TCCState *s1, int do_preprocess)
{
    int ret;
#if defined CONFIG_TCC_GDEBUG
    tcc_debug_start(s1);
#endif
    /* an elf symbol of type STT_FILE must be put so that STB_LOCAL symbols can be safely used */
    put_elf_sym( symtab_section, 0, 0, ELFW(ST_INFO)(STB_LOCAL, STT_FILE), 0, SHN_ABS, file->filename );
    /* default section is text */
    cur_text_section = text_section;
    ind = cur_text_section->data_offset;
    nocode_wanted = 0;
    ret = tcc_assemble_internal(s1, do_preprocess, 1);
    cur_text_section->data_offset = ind;
#if defined CONFIG_TCC_GDEBUG
    tcc_debug_end(s1);
#endif
    return ret;
}

/********************************************************************/
/* GCC inline asm support */

/* assemble the string 'str' in the current C compilation unit without
   C preprocessing. NOTE: str is modified by modifying the '\0' at the
   end */
static void tcc_assemble_inline(TCCState *s1, char *str, int len, int global)
{
    const int *saved_macro_ptr = macro_ptr;
    int dotid = set_idnum('.', IS_ID);

    tcc_open_bf(s1, ":asm:", len);
    memcpy(file->buffer, str, len);
    macro_ptr = NULL;
    tcc_assemble_internal(s1, 0, global);
    tcc_close();

    set_idnum('.', dotid);
    macro_ptr = saved_macro_ptr;
}

/* find a constraint by its number or id (gcc 3 extended
   syntax). return -1 if not found. Return in *pp in char after the
   constraint */
ST_FUNC int find_constraint(ASMOperand *operands, int nb_operands, 
                           const char *name, const char **pp)
{
    int index;
    TokenSym *ts;
    const char *p;

    if (isnum(*name)) {
        index = 0;
        while (isnum(*name)) {
            index = (index * 10) + (*name) - '0';
            name++;
        }
        if ((unsigned)index >= nb_operands)
            index = -1;
    } else if (*name == '[') {
        name++;
        p = strchr(name, ']');
        if (p) {
            ts = tok_alloc(name, p - name);
            for(index = 0; index < nb_operands; index++) {
                if (operands[index].id == ts->tok)
                    goto found;
            }
            index = -1;
        found:
            name = p + 1;
        } else {
            index = -1;
        }
    } else {
        index = -1;
    }
    if (pp)
        *pp = name;
    return index;
}

static void subst_asm_operands(ASMOperand *operands, int nb_operands, 
                               CString *out_str, CString *in_str)
{
    int c, index, modifier;
    const char *str;
    ASMOperand *op;
    SValue sv;

    cstr_new(out_str);
    str = in_str->data;
    for(;;) {
        c = *str++;
        if (c == '%') {
            if (*str == '%') {
                str++;
                goto add_char;
            }
            modifier = 0;
            if (*str == 'c' || *str == 'n' ||
                *str == 'b' || *str == 'w' || *str == 'h' || *str == 'k' ||
		*str == 'q' ||
		/* P in GCC would add "@PLT" to symbol refs in PIC mode,
		   and make literal operands not be decorated with '$'.  */
		*str == 'P')
                modifier = *str++;
            index = find_constraint(operands, nb_operands, str, &str);
            if( index < 0 )  tcc_error(-1, "invalid operand reference after %%");
            op = &operands[index];
            sv = *op->vt;
            if (op->reg >= 0) {
                sv.r = op->reg;
                if ((op->vt->r & VT_VALMASK) == VT_LLOCAL && op->is_memory)
                    sv.r |= VT_LVAL;
            }
            subst_asm_operand(out_str, &sv, modifier);
        } else {
        add_char:
            cstr_ccat(out_str, c);
            if (c == '\0')
                break;
        }
    }
}


static void parse_asm_operands(ASMOperand *operands, int *nb_operands_ptr,
                               int is_output)
{
    ASMOperand *op;
    int nb_operands;

    if (tok != ':') {
        nb_operands = *nb_operands_ptr;
        for(;;) {
	    CString astr;
            if( nb_operands >= MAX_ASM_OPERANDS )  tcc_error(-1, "too many asm operands");
            op = &operands[nb_operands++];
            op->id = 0;
            if (tok == '[') {
                next();
                if( tok < TOK_IDENT )  tcc_error(-1, "identifier expected" );
                op->id = tok;
                next();
                skip(']');
            }
	    parse_mult_str(&astr, "string constant");
            op->constraint = tcc_malloc(astr.size);
            strcpy(op->constraint, astr.data);
	    cstr_free(&astr);
            skip('(');
            gexpr();
            if (is_output) {
                if (!(vtop->type.t & VT_ARRAY))
                    test_lvalue();
            } else {
                /* we want to avoid LLOCAL case, except when the 'm'
                   constraint is used. Note that it may come from
                   register storage, so we need to convert (reg)
                   case */
                if ((vtop->r & VT_LVAL) &&
                    ((vtop->r & VT_VALMASK) == VT_LLOCAL ||
                     (vtop->r & VT_VALMASK) < VT_CONST) &&
                    !strchr(op->constraint, 'm')) {
                    gv(RC_INT);
                }
            }
            op->vt = vtop;
            skip(')');
            if (tok == ',') {
                next();
            } else {
                break;
            }
        }
        *nb_operands_ptr = nb_operands;
    }
}

/* parse the GCC asm() instruction */
ST_FUNC void asm_instr(void)
{
    CString astr, astr1;
    ASMOperand operands[MAX_ASM_OPERANDS];
    int nb_outputs, nb_operands, i, must_subst, out_reg;
    uint8_t clobber_regs[NB_ASM_REGS];

    next();
    /* since we always generate the asm() instruction, we can ignore
       volatile */
    if (tok == TOK_VOLATILE1 || tok == TOK_VOLATILE2 || tok == TOK_VOLATILE3) {
        next();
    }
    parse_asm_str(&astr);
    nb_operands = 0;
    nb_outputs = 0;
    must_subst = 0;
    memset(clobber_regs, 0, sizeof(clobber_regs));
    if (tok == ':') {
        next();
        must_subst = 1;
        /* output args */
        parse_asm_operands(operands, &nb_operands, 1);
        nb_outputs = nb_operands;
        if (tok == ':') {
            next();
            if (tok != ')') {
                /* input args */
                parse_asm_operands(operands, &nb_operands, 0);
                if (tok == ':') {
                    /* clobber list */
                    /* XXX: handle registers */
                    next();
                    for(;;) {
                        if( tok != TOK_STR )  tcc_error(-1, "string constant expected" );
                        asm_clobber(clobber_regs, tokc.str.data);
                        next();
                        if (tok == ',') {
                            next();
                        } else {
                            break;
                        }
                    }
                }
            }
        }
    }
    skip(')');
    /* NOTE: we do not eat the ';' so that we can restore the current
       token after the assembler parsing */
    if( tok != ';' )  tcc_error(-1, "';' expected" );
    
    /* save all values in the memory */
    save_regs(0);

    /* compute constraints */
    asm_compute_constraints(operands, nb_operands, nb_outputs, 
                            clobber_regs, &out_reg);

    /* substitute the operands in the asm string. No substitution is
       done if no operands (GCC behaviour) */
#ifdef ASM_DEBUG
    printf("asm: \"%s\"\n", (char *)astr.data);
#endif
    if (must_subst) {
        subst_asm_operands(operands, nb_operands, &astr1, &astr);
        cstr_free(&astr);
    } else {
        astr1 = astr;
    }
#ifdef ASM_DEBUG
    printf("subst_asm: \"%s\"\n", (char *)astr1.data);
#endif

    /* generate loads */
    asm_gen_code(operands, nb_operands, nb_outputs, 0, 
                 clobber_regs, out_reg);    

    /* assemble the string with tcc internal assembler */
    tcc_assemble_inline(tcc_state, astr1.data, astr1.size - 1, 0);

    /* restore the current C token */
    next();

    /* store the output values if needed */
    asm_gen_code(operands, nb_operands, nb_outputs, 1, 
                 clobber_regs, out_reg);
    
    /* free everything */
    for(i=0;i<nb_operands;i++) {
        ASMOperand *op;
        op = &operands[i];
        tcc_free(op->constraint);
        vpop();
    }
    cstr_free(&astr1);
}

ST_FUNC void asm_global_instr(void)
{
    CString astr;
    int saved_nocode_wanted = nocode_wanted;

    /* Global asm blocks are always emitted.  */
    nocode_wanted = 0;
    next();
    parse_asm_str(&astr);
    skip(')');
    /* NOTE: we do not eat the ';' so that we can restore the current
       token after the assembler parsing */
    if( tok != ';' )  tcc_error(-1, "';' expected" );
    
#ifdef ASM_DEBUG
    printf("asm_global: \"%s\"\n", (char *)astr.data);
#endif
    cur_text_section = text_section;
    ind = cur_text_section->data_offset;

    /* assemble the string with tcc internal assembler */
    tcc_assemble_inline(tcc_state, astr.data, astr.size - 1, 1);
    
    cur_text_section->data_offset = ind;

    /* restore the current C token */
    next();

    cstr_free(&astr);
    nocode_wanted = saved_nocode_wanted;
}
#endif /* CONFIG_TCC_ASM */

#endif
#endif /* ONE_SOURCE */

/********************************************************/
#ifndef CONFIG_TCC_ASM
ST_FUNC void asm_instr(void)
{
    tcc_error(-1, "inline asm() not supported");
}
ST_FUNC void asm_global_instr(void)
{
    tcc_error(-1, "inline asm() not supported");
}
#endif

/********************************************************/
#ifdef _WIN32
ST_FUNC char *normalize_slashes(char *path)
{
    char *p;
    for (p = path; *p; ++p)
        if (*p == '\\')
            *p = '/';
    return path;
}

static HMODULE tcc_module;

/* on win32, we suppose the lib and includes are at the location of 'tcc.exe' */
static void tcc_set_lib_path_w32(TCCState *s)
{
    char path[1024], *p;
    GetModuleFileNameA(tcc_module, path, sizeof path);
    p = tcc_basename(normalize_slashes(strlwr(path)));
    if (p > path)
        --p;
    *p = 0;
    tcc_set_lib_path(s, path);
}

#ifdef TCC_TARGET_PE
static void tcc_add_systemdir(TCCState *s)
{
    char buf[1000];
    GetSystemDirectory(buf, sizeof buf);
    tcc_add_library_path(s, normalize_slashes(buf));
}
#endif

#ifdef LIBTCC_AS_DLL
BOOL WINAPI DllMain (HINSTANCE hDll, DWORD dwReason, LPVOID lpReserved)
{
    if (DLL_PROCESS_ATTACH == dwReason)
        tcc_module = hDll;
    return TRUE;
}
#endif
#endif

/********************************************************/
/* copy a string and truncate it. */
ST_FUNC char *pstrcpy(char *buf, int buf_size, const char *s)
{
    char *q, *q_end;
    int c;

    if (buf_size > 0) {
        q = buf;
        q_end = buf + buf_size - 1;
        while (q < q_end) {
            c = *s++;
            if (c == '\0')
                break;
            *q++ = c;
        }
        *q = '\0';
    }
    return buf;
}

/* strcat and truncate. */
ST_FUNC char *pstrcat(char *buf, int buf_size, const char *s)
{
    int len;
    len = strlen(buf);
    if (len < buf_size)
        pstrcpy(buf + len, buf_size - len, s);
    return buf;
}

ST_FUNC char *pstrncpy(char *out, const char *in, size_t num)
{
    memcpy(out, in, num);
    out[num] = '\0';
    return out;
}

/* extract the basename of a file */
PUB_FUNC char *tcc_basename(const char *name)
{
    char *p = strchr(name, 0);
    while (p > name && !IS_DIRSEP(p[-1]))
        --p;
    return p;
}

/* extract extension part of a file
 *
 * (if no extension, return pointer to end-of-string)
 */
PUB_FUNC char *tcc_fileextension (const char *name)
{
    char *b = tcc_basename(name);
    char *e = strrchr(b, '.');
    return e ? e : strchr(b, 0);
}

/********************************************************/
/* memory management */

#undef free
#undef malloc
#undef realloc

#ifndef MEM_DEBUG

PUB_FUNC void tcc_free(void *ptr) { free(ptr); }

PUB_FUNC void *tcc_malloc(unsigned long size)
{
    void *ptr;
    ptr = malloc(size);
    if( !ptr && size )  tcc_error(-1, "memory full (malloc)");
    return ptr;
}

PUB_FUNC void *tcc_mallocz(unsigned long size)
{
    void *ptr;
    ptr = tcc_malloc(size);
    memset(ptr, 0, size);
    return ptr;
}

PUB_FUNC void *tcc_realloc(void *ptr, unsigned long size)
{
    void *ptr1;
    ptr1 = realloc(ptr, size);
    if( !ptr1 && size )  tcc_error(-1, "memory full (realloc)");
    return ptr1;
}

PUB_FUNC char *tcc_strdup(const char *str)
{
    char *ptr;
    ptr = tcc_malloc(strlen(str) + 1);
    strcpy(ptr, str);
    return ptr;
}

#else

#define MEM_DEBUG_MAGIC1 0xFEEDDEB1
#define MEM_DEBUG_MAGIC2 0xFEEDDEB2
#define MEM_DEBUG_MAGIC3 0xFEEDDEB3
#define MEM_DEBUG_FILE_LEN 40
#define MEM_DEBUG_CHECK3(header) \
    ((mem_debug_header_t*)((char*)header + header->size))->magic3
#define MEM_USER_PTR(header) \
    ((char *)header + offsetof(mem_debug_header_t, magic3))
#define MEM_HEADER_PTR(ptr) \
    (mem_debug_header_t *)((char*)ptr - offsetof(mem_debug_header_t, magic3))

struct mem_debug_header {
    unsigned magic1;
    unsigned size;
    struct mem_debug_header *prev;
    struct mem_debug_header *next;
    int line_num;
    char file_name[MEM_DEBUG_FILE_LEN + 1];
    unsigned magic2;
    ALIGNED(16) unsigned magic3;
};

typedef struct mem_debug_header mem_debug_header_t;

static mem_debug_header_t *mem_debug_chain;
static unsigned mem_cur_size;
static unsigned mem_max_size;

static mem_debug_header_t *malloc_check(void *ptr, const char *msg)
{
    mem_debug_header_t * header = MEM_HEADER_PTR(ptr);
    if (header->magic1 != MEM_DEBUG_MAGIC1 ||
        header->magic2 != MEM_DEBUG_MAGIC2 ||
        MEM_DEBUG_CHECK3(header) != MEM_DEBUG_MAGIC3 ||
        header->size == (unsigned)-1) {
        fprintf(stderr, "%s check failed\n", msg);
        if (header->magic1 == MEM_DEBUG_MAGIC1)
            fprintf(stderr, "%s:%u: block allocated here.\n",
                header->file_name, header->line_num);
        exit( -201 );  // JJX  used to be:   exit(1);
    }
    return header;
}

PUB_FUNC void *tcc_malloc_debug(unsigned long size, const char *file, int line)
{
    int ofs;
    mem_debug_header_t *header;

    header = malloc(sizeof(mem_debug_header_t) + size);
    if( !header )  tcc_error(-1, "memory full (malloc)");

    header->magic1 = MEM_DEBUG_MAGIC1;
    header->magic2 = MEM_DEBUG_MAGIC2;
    header->size = size;
    MEM_DEBUG_CHECK3(header) = MEM_DEBUG_MAGIC3;
    header->line_num = line;
    ofs = strlen(file) - MEM_DEBUG_FILE_LEN;
    strncpy(header->file_name, file + (ofs > 0 ? ofs : 0), MEM_DEBUG_FILE_LEN);
    header->file_name[MEM_DEBUG_FILE_LEN] = 0;

    header->next = mem_debug_chain;
    header->prev = NULL;
    if (header->next)
        header->next->prev = header;
    mem_debug_chain = header;

    mem_cur_size += size;
    if (mem_cur_size > mem_max_size)
        mem_max_size = mem_cur_size;

    return MEM_USER_PTR(header);
}

PUB_FUNC void tcc_free_debug(void *ptr)
{
    mem_debug_header_t *header;
    if (!ptr)
        return;
    header = malloc_check(ptr, "tcc_free");
    mem_cur_size -= header->size;
    header->size = (unsigned)-1;
    if (header->next)
        header->next->prev = header->prev;
    if (header->prev)
        header->prev->next = header->next;
    if (header == mem_debug_chain)
        mem_debug_chain = header->next;
    free(header);
}

PUB_FUNC void *tcc_mallocz_debug(unsigned long size, const char *file, int line)
{
    void *ptr;
    ptr = tcc_malloc_debug(size,file,line);
    memset(ptr, 0, size);
    return ptr;
}

PUB_FUNC void *tcc_realloc_debug(void *ptr, unsigned long size, const char *file, int line)
{
    mem_debug_header_t *header;
    int mem_debug_chain_update = 0;
    if (!ptr)
        return tcc_malloc_debug(size, file, line);
    header = malloc_check(ptr, "tcc_realloc");
    mem_cur_size -= header->size;
    mem_debug_chain_update = (header == mem_debug_chain);
    header = realloc(header, sizeof(mem_debug_header_t) + size);
    if( !header )  tcc_error(-1, "memory full (realloc)");
    header->size = size;
    MEM_DEBUG_CHECK3(header) = MEM_DEBUG_MAGIC3;
    if (header->next)
        header->next->prev = header;
    if (header->prev)
        header->prev->next = header;
    if (mem_debug_chain_update)
        mem_debug_chain = header;
    mem_cur_size += size;
    if (mem_cur_size > mem_max_size)
        mem_max_size = mem_cur_size;
    return MEM_USER_PTR(header);
}

PUB_FUNC char *tcc_strdup_debug(const char *str, const char *file, int line)
{
    char *ptr;
    ptr = tcc_malloc_debug(strlen(str) + 1, file, line);
    strcpy(ptr, str);
    return ptr;
}

PUB_FUNC void tcc_memcheck(void)
{
    if (mem_cur_size) {
        mem_debug_header_t *header = mem_debug_chain;
        fprintf(stderr, "MEM_DEBUG: mem_leak= %d bytes, mem_max_size= %d bytes\n",
            mem_cur_size, mem_max_size);
        while (header) {
            fprintf(stderr, "%s:%u: error: %u bytes leaked\n",
                header->file_name, header->line_num, header->size);
            header = header->next;
        }
#if MEM_DEBUG-0 == 2
        exit( -204 );  // JJX  used to be:   exit(2);
#endif
    }
}
#endif /* MEM_DEBUG */

#define free(p) use_tcc_free(p)
#define malloc(s) use_tcc_malloc(s)
#define realloc(p, s) use_tcc_realloc(p, s)

/********************************************************/
/* dynarrays */

ST_FUNC void dynarray_add(void *ptab, int *nb_ptr, void *data)
{
    int nb, nb_alloc;
    void **pp;

    nb = *nb_ptr;
    pp = *(void ***)ptab;
    /* every power of two we double array size */
    if ((nb & (nb - 1)) == 0) {
        if (!nb)
            nb_alloc = 1;
        else
            nb_alloc = nb * 2;
        pp = tcc_realloc(pp, nb_alloc * sizeof(void *));
        *(void***)ptab = pp;
    }
    pp[nb++] = data;
    *nb_ptr = nb;
}

ST_FUNC void dynarray_reset(void *pp, int *n)
{
    void **p;
    for (p = *(void***)pp; *n; ++p, --*n)
       if(*p)  tcc_free(*p);
    tcc_free(*(void**)pp);
    *(void**)pp = NULL;
}

static void tcc_split_path(TCCState *s, void *p_ary, int *p_nb_ary, const char *in)
{
    const char *p;
    do {
        int c;
        CString str;

        cstr_new(&str);
        for (p = in; c = *p, c != '\0' && c != PATHSEP[0]; ++p) {
            if (c == '{' && p[1] && p[2] == '}') {
                c = p[1], p += 2;
                if (c == 'B')
                    cstr_cat(&str, s->tcc_lib_path, -1);
            } else {
                cstr_ccat(&str, c);
            }
        }
        if (str.size) {
            cstr_ccat(&str, '\0');
            dynarray_add(p_ary, p_nb_ary, tcc_strdup(str.data));
        }
        cstr_free(&str);
        in = p+1;
    } while (*p);
}

/********************************************************/

static void strcat_vprintf(char *buf, int buf_size, const char *fmt, va_list ap) {
    int  len = strlen(buf);
    vsnprintf(buf + len, buf_size - len, fmt, ap);
}
static void strcat_printf(char *buf, int buf_size, const char *fmt, ...) {
    va_list  ap;
    va_start(ap, fmt);
    strcat_vprintf(buf, buf_size, fmt, ap);
    va_end(ap);
}


PUB_FUNC void tcc_error( int etype, const char *fmt, ... ) {

    char  buf[ 2048 ];
    BufferedFile **pf = NULL;
    BufferedFile  *f  = NULL;
    va_list  ap;
    TCCState * s1 = NULL;
    // JJX  (int) etype == -1   it's an (abort) error
    // JJX              ==  0   it's a  warning
    // JJX              ==  1   it's a  noabort-error
    buf[0] = '\0';

    if( 1 == jjglob_newdone && NULL != tcc_state ) {
       s1 = tcc_state;
       if( !etype && !s1->do_warn ) { jjglob_retval = -2; return; }  // a warning
    }
    else {
       if( !etype ) { jjglob_retval = -2; return; }  // a warning
    }
    va_start(ap, fmt);
    /* use upper file if inline ":asm:" or token ":paste:" */
    if( file ) {
       f = file;
       for( ; f && ':' == f->filename[0]; f = f->prev ) { }
    }
    if( f ) {
       if( s1 ) {
          for( pf = s1->include_stack; pf < s1->include_stack_ptr; pf++ ) {
             strcat_printf( buf, sizeof(buf), "In file included from %s:%d:\n", (*pf)->filename, (*pf)->line_num );
          }
       }
       if( 2 == jmp_var ) {
          strcat_printf( buf, sizeof(buf), "%s:%d: ", f->filename, f->line_num - !!(tok_flags & TOK_FLAG_BOL));
       }
       else  strcat_printf( buf, sizeof(buf), "%s: ", f->filename );
    }
    else  strcat_printf( buf, sizeof(buf), "tcc: " );
    if     ( 0 == etype )  strcat_printf( buf, sizeof(buf), "warning: "       );
    else if( 1 == etype )  strcat_printf( buf, sizeof(buf), "error-noabort: " );
    else /* -1 == etype */ strcat_printf( buf, sizeof(buf), "error-abort: "   );
    strcat_vprintf( buf, sizeof(buf), fmt, ap );
    // JJX  if( s1 && s1->error_func )  s1->error_func( s1->error_opaque, buf );
    // JJX  else {
       if( !jjglob_dbgfh ) {  // not opend yet
          jjglob_retval = memfd_create( "jitcc_error_memfd", (unsigned int) 0 );
          if( -1 == jjglob_retval )  jjglob_retval = -18;  // could not open it
          else  jjglob_dbgfh = fdopen( jjglob_retval, "r+b" );  // O_RDWR
       }
       else {  // we have an open fh
          if( 0 > jjglob_retval ) {
             if( !etype )  jjglob_retval = -2;  // a warning
             else {
                jjglob_retval = fileno( jjglob_dbgfh );
                if( -1 == jjglob_retval )  jjglob_retval = -19;
             }
          }
       }
       if( jjglob_dbgfh ) {
          (void) fprintf( jjglob_dbgfh, "%s\n", buf );
          // JJX  (void) fflush( jjglob_dbgfh );  // JJX  will be fflush()ed in jitcc()
       }
    // JJX  }

    if( s1 && ( etype || s1->warn_error ))  s1->nb_errors++;
    va_end(ap);
    if( -1 < etype ) return;
    if( 2 == jmp_var )  longjmp( err_jmp_buf2, 2 );
    if( 1 == jmp_var )  longjmp( err_jmp_buf1, 1 );

  exit( -203 );  // JJX  used to be:   exit( 1 );
}


// JJX  Omitted for now:
// JJX  LIBTCCAPI void tcc_set_error_func(TCCState *s, void *error_opaque, void (*error_func)(void *opaque, const char *msg)) {
// JJX      s->error_opaque = error_opaque;
// JJX      s->error_func = error_func; }


/********************************************************/
/* I/O layer */

ST_FUNC void tcc_open_bf(TCCState *s1, const char *filename, int initlen)
{
    BufferedFile *bf;
    int buflen = initlen ? initlen : IO_BUF_SIZE;

    bf = tcc_mallocz(sizeof(BufferedFile) + buflen);
    bf->buf_ptr = bf->buffer;
    bf->buf_end = bf->buffer + initlen;
    bf->buf_end[0] = CH_EOB; /* put eob symbol */
    pstrcpy(bf->filename, sizeof(bf->filename), filename);
    bf->true_filename = bf->filename;
    bf->line_num = 1;
    bf->ifdef_stack_ptr = s1->ifdef_stack_ptr;
    bf->fd = -1;
    bf->prev = file;
    file = bf;
    tok_flags = TOK_FLAG_BOL | TOK_FLAG_BOF;
}

ST_FUNC void tcc_close(void)
{
    BufferedFile *bf = file;
    if (bf->fd > 0) {
        close(bf->fd);
        total_lines += bf->line_num;
    }
    if (bf->true_filename != bf->filename)
        tcc_free(bf->true_filename);
    file = bf->prev;
    tcc_free(bf);
}

ST_FUNC int tcc_open(TCCState *s1, const char *filename)
{
    int fd;
    if (strcmp(filename, "-") == 0) { fd = 0; filename = "<stdin>"; }
    else  fd = open(filename, O_RDONLY | O_BINARY);
    if( s1->verbose && fd >= 0 )
       (void) fprintf( jjglob_dbgfh, " JJVERBOSE:  %s %*s%s\n", fd < 0 ? "nf":"->", (int)(s1->include_stack_ptr - s1->include_stack), "", filename );
    if( 0 > fd )  return -1;
    tcc_open_bf(s1, filename, 0);
    file->fd = fd;
    return fd;
}

/* compile the file opened in 'file'. Return non zero if errors. */
static int tcc_compile( TCCState *s1 ) {
    Sym *define_start;
    int filetype, is_asm;
    define_start = define_stack;
    filetype = s1->filetype;
    is_asm = filetype == AFF_TYPE_ASM || filetype == AFF_TYPE_ASMPP;
    tccelf_begin_file(s1);
    if( !setjmp( err_jmp_buf2 )) {
        jmp_var = 2;
        s1->nb_errors   = 0;
        preprocess_start(s1, is_asm);
        if( is_asm ) {
#ifdef CONFIG_TCC_ASM
           tcc_assemble(s1, filetype == AFF_TYPE_ASMPP);
#else
           tcc_error(1, "asm not supported");
#endif
        }
        else  tccgen_compile( s1 );
    }
    jmp_var = 1;
    preprocess_end( s1 );
    free_inline_functions(s1);
    /* reset define stack, but keep -D and built-ins */
    free_defines(define_start);
    sym_pop(&global_stack, NULL, 0);
    sym_pop(&local_stack, NULL, 0);
    tccelf_end_file(s1);
  return s1->nb_errors != 0 ? -1 : 0;
}

LIBTCCAPI int tcc_compile_string(TCCState *s, const char *str)
{
    int len, ret;
    len = strlen(str);
    tcc_open_bf(s, "<string>", len);
    memcpy(file->buffer, str, len);
    ret = tcc_compile(s);
    tcc_close();
    return ret;
}

/* define a preprocessor symbol. A value can also be provided with the '=' operator */
LIBTCCAPI void tcc_define_symbol(TCCState *s1, const char *sym, const char *value)
{
    int len1, len2;
    /* default value */
    if (!value)
        value = "1";
    len1 = strlen(sym);
    len2 = strlen(value);

    /* init file structure */
    tcc_open_bf(s1, "<define>", len1 + len2 + 1);
    memcpy(file->buffer, sym, len1);
    file->buffer[len1] = ' ';
    memcpy(file->buffer + len1 + 1, value, len2);

    /* parse with define parser */
    next_nomacro();
    parse_define();
    tcc_close();
}

/* undefine a preprocessor symbol */
LIBTCCAPI void tcc_undefine_symbol(TCCState *s1, const char *sym)
{
    TokenSym *ts;
    Sym *s;
    ts = tok_alloc(sym, strlen(sym));
    s = define_find(ts->tok);
    /* undefine symbol by putting an invalid name */
    if (s)
        define_undef(s);
}

/* cleanup all static data used during compilation */
static void tcc_cleanup(void)
{
    if( NULL == tcc_state ) return;
    while( file )  tcc_close();
    tccpp_delete(tcc_state);
    tcc_state = NULL;
    dynarray_reset(&sym_pools, &nb_sym_pools);  // free sym_pools
    sym_free_first = NULL;  // reset symbol stack
}

LIBTCCAPI TCCState *tcc_new(void)
{
    TCCState *s;
    tcc_cleanup();

    s = tcc_mallocz(sizeof(TCCState));
    if( !s ) return NULL;
    tcc_state = s;
    ++nb_states;

    // s->no_alacarte_link = 0;  // its already zeroed-out
    s->nocommon = 1;
    s->warn_implicit_function_declaration = 1;
    s->ms_extensions = 1;

#ifdef CHAR_IS_UNSIGNED
    s->char_is_unsigned = 1;
#endif
#ifdef TCC_TARGET_I386
    s->seg_size = 32;
#endif
    /* enable this if you want symbols with leading underscore on windows: */
    tcc_set_lib_path(s, CONFIG_TCCDIR);
    tccelf_new(s);
    tccpp_new(s);

    /* we add dummy defines for some special macros to speed up tests
       and to have working defined() */
    define_push(TOK___LINE__, MACRO_OBJ, NULL, NULL);
    define_push(TOK___FILE__, MACRO_OBJ, NULL, NULL);
    define_push(TOK___DATE__, MACRO_OBJ, NULL, NULL);
    define_push(TOK___TIME__, MACRO_OBJ, NULL, NULL);
    define_push(TOK___COUNTER__, MACRO_OBJ, NULL, NULL);

    tcc_define_symbol(s, "__TINYC__", "1" );

    /* standard defines */
    tcc_define_symbol(s, "__STDC__", NULL);
    tcc_define_symbol(s, "__STDC_VERSION__", "199901L");
    tcc_define_symbol(s, "__STDC_HOSTED__", NULL);

    /* target defines */
#if defined(TCC_TARGET_I386)
    tcc_define_symbol(s, "__i386__", NULL);
    tcc_define_symbol(s, "__i386", NULL);
    tcc_define_symbol(s, "i386", NULL);
#elif defined(TCC_TARGET_X86_64)
    tcc_define_symbol(s, "__x86_64__", NULL);
#elif defined(TCC_TARGET_ARM)
    tcc_define_symbol(s, "__ARM_ARCH_4__", NULL);
    tcc_define_symbol(s, "__arm_elf__", NULL);
    tcc_define_symbol(s, "__arm_elf", NULL);
    tcc_define_symbol(s, "arm_elf", NULL);
    tcc_define_symbol(s, "__arm__", NULL);
    tcc_define_symbol(s, "__arm", NULL);
    tcc_define_symbol(s, "arm", NULL);
    tcc_define_symbol(s, "__APCS_32__", NULL);
    tcc_define_symbol(s, "__ARMEL__", NULL);
#if defined(TCC_ARM_EABI)
    tcc_define_symbol(s, "__ARM_EABI__", NULL);
#endif
#if defined(TCC_ARM_HARDFLOAT)
    s->float_abi = ARM_HARD_FLOAT;
    tcc_define_symbol(s, "__ARM_PCS_VFP", NULL);
#else
    s->float_abi = ARM_SOFTFP_FLOAT;
#endif
#elif defined(TCC_TARGET_ARM64)
    tcc_define_symbol(s, "__aarch64__", NULL);
#elif defined TCC_TARGET_C67
    tcc_define_symbol(s, "__C67__", NULL);
#endif

    tcc_define_symbol(s, "__unix__", NULL);
    tcc_define_symbol(s, "__unix", NULL);
    tcc_define_symbol(s, "unix", NULL);
# if defined(__linux__)
    tcc_define_symbol(s, "__linux__", NULL);
    tcc_define_symbol(s, "__linux", NULL);
# endif
# if defined(__FreeBSD__)
    tcc_define_symbol(s, "__FreeBSD__", "__FreeBSD__");
    /* No 'Thread Storage Local' on FreeBSD with tcc */
    tcc_define_symbol(s, "__NO_TLS", NULL);
# endif
# if defined(__FreeBSD_kernel__)
    tcc_define_symbol(s, "__FreeBSD_kernel__", NULL);
# endif
# if defined(__NetBSD__)
    tcc_define_symbol(s, "__NetBSD__", "__NetBSD__");
# endif
# if defined(__OpenBSD__)
    tcc_define_symbol(s, "__OpenBSD__", "__OpenBSD__");
# endif

    /* TinyCC & gcc defines */
#if PTR_SIZE == 4
    /* 32bit systems. */
    tcc_define_symbol(s, "__SIZE_TYPE__", "unsigned int");
    tcc_define_symbol(s, "__PTRDIFF_TYPE__", "int");
    tcc_define_symbol(s, "__ILP32__", NULL);
#elif LONG_SIZE == 4
    /* 64bit Windows. */
    tcc_define_symbol(s, "__SIZE_TYPE__", "unsigned long long");
    tcc_define_symbol(s, "__PTRDIFF_TYPE__", "long long");
    tcc_define_symbol(s, "__LLP64__", NULL);
#else
    /* Other 64bit systems. */
    tcc_define_symbol(s, "__SIZE_TYPE__", "unsigned long");
    tcc_define_symbol(s, "__PTRDIFF_TYPE__", "long");
    tcc_define_symbol(s, "__LP64__", NULL);
#endif

    tcc_define_symbol(s, "__WCHAR_TYPE__", "int");
    /* wint_t is unsigned int by default, but (signed) int on BSDs
       and unsigned short on windows.  Other OSes might have still
       other conventions, sigh.  */
# if defined(__FreeBSD__) || defined (__FreeBSD_kernel__) \
  || defined(__NetBSD__) || defined(__OpenBSD__)
    tcc_define_symbol(s, "__WINT_TYPE__", "int");
#  ifdef __FreeBSD__
    /* define __GNUC__ to have some useful stuff from sys/cdefs.h
       that are unconditionally used in FreeBSDs other system headers :/ */
    tcc_define_symbol(s, "__GNUC__", "2");
    tcc_define_symbol(s, "__GNUC_MINOR__", "7");
    tcc_define_symbol(s, "__builtin_alloca", "alloca");
#  endif
# else
    tcc_define_symbol(s, "__WINT_TYPE__", "unsigned int");
    /* glibc defines */
    tcc_define_symbol(s, "__REDIRECT(name, proto, alias)", "name proto __asm__ (#alias)");
    tcc_define_symbol(s, "__REDIRECT_NTH(name, proto, alias)", "name proto __asm__ (#alias) __THROW");
# endif
# if defined(TCC_MUSL)
    tcc_define_symbol(s, "__DEFINED_va_list", "");
    tcc_define_symbol(s, "__DEFINED___isoc_va_list", "");
    tcc_define_symbol(s, "__isoc_va_list", "void *");
# endif /* TCC_MUSL */
    /* Some GCC builtins that are simple to express as macros.  */
    tcc_define_symbol(s, "__builtin_extract_return_addr(x)", "x");
    return s;
}

LIBTCCAPI void tcc_delete(TCCState *s1)
{
    tcc_cleanup();

    /* free sections */
    tccelf_delete(s1);

    /* free library paths */
    dynarray_reset(&s1->library_paths, &s1->nb_library_paths);
    dynarray_reset(&s1->crt_paths, &s1->nb_crt_paths);

    /* free include paths */
    dynarray_reset(&s1->cached_includes, &s1->nb_cached_includes);
    dynarray_reset(&s1->include_paths, &s1->nb_include_paths);
    dynarray_reset(&s1->sysinclude_paths, &s1->nb_sysinclude_paths);
    dynarray_reset(&s1->cmd_include_files, &s1->nb_cmd_include_files);

    tcc_free(s1->tcc_lib_path);
    tcc_free(s1->soname);
    tcc_free(s1->rpath);
    tcc_free(s1->init_symbol);
    tcc_free(s1->fini_symbol);
    dynarray_reset(&s1->files, &s1->nb_files);
    dynarray_reset(&s1->target_deps, &s1->nb_target_deps);
    dynarray_reset(&s1->pragma_libs, &s1->nb_pragma_libs);
    // JJX  eliminated:  dynarray_reset(&s1->argv, &s1->argc);

#ifdef TCC_IS_NATIVE
    /* free runtime memory */
    tcc_run_free(s1);
#endif

    tcc_free(s1);
#ifdef MEM_DEBUG
    if( 0 == --nb_states )  tcc_memcheck();
#endif
}

// LIBTCCAPI int tcc_set_output_type(TCCState *s, int output_type) { ... }

LIBTCCAPI int tcc_add_include_path(TCCState *s, const char *pathname)
{
    tcc_split_path(s, &s->include_paths, &s->nb_include_paths, pathname);
    return 0;
}

LIBTCCAPI int tcc_add_sysinclude_path(TCCState *s, const char *pathname)
{
    tcc_split_path(s, &s->sysinclude_paths, &s->nb_sysinclude_paths, pathname);
    return 0;
}

ST_FUNC int tcc_add_file_internal(TCCState *s1, const char *filename, int flags)
{
    int ret;

    /* open the file */
    ret = tcc_open(s1, filename);
    if (ret < 0) {
        if (flags & AFF_PRINT_ERROR)
            tcc_error(1, "file '%s' not found", filename);
        return ret;
    }

    /* update target deps */
    dynarray_add(&s1->target_deps, &s1->nb_target_deps,
            tcc_strdup(filename));

    if (flags & AFF_TYPE_BIN) {
        ElfW(Ehdr) ehdr;
        int fd, obj_type;

        fd = file->fd;
        obj_type = tcc_object_type(fd, &ehdr);
        lseek(fd, 0, SEEK_SET);

#ifdef TCC_TARGET_MACHO
        if (0 == obj_type && 0 == strcmp(tcc_fileextension(filename), ".dylib"))
            obj_type = AFF_BINTYPE_DYN;
#endif

        switch (obj_type) {
        case AFF_BINTYPE_REL:
            ret = tcc_load_object_file(s1, fd, 0);
            break;
#ifndef TCC_TARGET_PE
        case AFF_BINTYPE_DYN:
            if (s1->output_type == TCC_OUTPUT_MEMORY) {
                ret = 0;
#ifdef TCC_IS_NATIVE
                if (NULL == dlopen(filename, RTLD_GLOBAL | RTLD_LAZY))
                    ret = -1;
#endif
            } else {
                ret = tcc_load_dll(s1, fd, filename,
                                   (flags & AFF_REFERENCED_DLL) != 0);
            }
            break;
#endif
        case AFF_BINTYPE_AR:
            ret = tcc_load_archive(s1, fd);
            break;
#ifdef TCC_TARGET_COFF
        case AFF_BINTYPE_C67:
            ret = tcc_load_coff(s1, fd);
            break;
#endif
        default:
            /* as GNU ld, consider it is an ld script if not recognized */
            ret = tcc_load_ldscript(s1);
            if( ret < 0 )  tcc_error(1, "unrecognized file type");
            break;
        }
    } else {
        ret = tcc_compile(s1);
    }
    tcc_close();
    return ret;
}

LIBTCCAPI int tcc_add_file(TCCState *s, const char *filename)
{
    int filetype = s->filetype;
    int flags = AFF_PRINT_ERROR;
    if (filetype == 0) {
        /* use a file extension to detect a filetype */
        const char *ext = tcc_fileextension(filename);
        if (ext[0]) {
            ext++;
            if (!strcmp(ext, "S"))
                filetype = AFF_TYPE_ASMPP;
            else if (!strcmp(ext, "s"))
                filetype = AFF_TYPE_ASM;
            else if (!PATHCMP(ext, "c") || !PATHCMP(ext, "i"))
                filetype = AFF_TYPE_C;
            else
                flags |= AFF_TYPE_BIN;
        } else {
            filetype = AFF_TYPE_C;
        }
        s->filetype = filetype;
    }
    return tcc_add_file_internal(s, filename, flags);
}

LIBTCCAPI int tcc_add_library_path(TCCState *s, const char *pathname)
{
    tcc_split_path(s, &s->library_paths, &s->nb_library_paths, pathname);
    return 0;
}

static int tcc_add_library_internal(TCCState *s, const char *fmt,
    const char *filename, int flags, char **paths, int nb_paths)
{
    char buf[1024];
    int i;

    for(i = 0; i < nb_paths; i++) {
        snprintf(buf, sizeof(buf), fmt, paths[i], filename);
        if (tcc_add_file_internal(s, buf, flags | AFF_TYPE_BIN) == 0)
            return 0;
    }
    return -1;
}

/* find and load a dll. Return non zero if not found */
/* XXX: add '-rpath' option support ? */
ST_FUNC int tcc_add_dll(TCCState *s, const char *filename, int flags)
{
    return tcc_add_library_internal(s, "%s/%s", filename, flags,
        s->library_paths, s->nb_library_paths);
}

ST_FUNC int tcc_add_crt(TCCState *s, const char *filename)
{
    if (-1 == tcc_add_library_internal(s, "%s/%s",
        filename, 0, s->crt_paths, s->nb_crt_paths))
        tcc_error(1, "file '%s' not found", filename);
    return 0;
}

/* the library name is the same as the argument of the '-l' option */
LIBTCCAPI int tcc_add_library(TCCState *s, const char *libraryname)
{
#if defined TCC_TARGET_MACHO
    const char *libs[] = { "%s/lib%s.dylib", "%s/lib%s.a", NULL };
    const char **pp = s->static_link ? libs + 1 : libs;
#else
    const char *libs[] = { "%s/lib%s.so", "%s/lib%s.a", NULL };
    const char **pp = s->static_link ? libs + 1 : libs;
#endif
    while (*pp) {
        if (0 == tcc_add_library_internal(s, *pp,
            libraryname, 0, s->library_paths, s->nb_library_paths))
            return 0;
        ++pp;
    }
    return -1;
}

PUB_FUNC int tcc_add_library_err(TCCState *s, const char *libname)
{
    int ret = tcc_add_library(s, libname);
    if( ret < 0 )  tcc_error(1, "library '%s' not found", libname);
    return ret;
}

/* handle #pragma comment(lib,) */
ST_FUNC void tcc_add_pragma_libs(TCCState *s1)
{
    int i;
    for (i = 0; i < s1->nb_pragma_libs; i++)
        tcc_add_library_err(s1, s1->pragma_libs[i]);
}

LIBTCCAPI int tcc_add_symbol(TCCState *s, const char *name, const void *val)
{
#ifdef TCC_TARGET_PE
    /* On x86_64 'val' might not be reachable with a 32bit offset.
       So it is handled here as if it were in a DLL. */
    pe_putimport(s, 0, name, (uintptr_t)val);
#else
    set_elf_sym(symtab_section, (uintptr_t)val, 0,
        ELFW(ST_INFO)(STB_GLOBAL, STT_NOTYPE), 0,
        SHN_ABS, name);
#endif
    return 0;
}

LIBTCCAPI void tcc_set_lib_path(TCCState *s, const char *path)
{
    tcc_free(s->tcc_lib_path);
    s->tcc_lib_path = tcc_strdup(path);
}

#define WD_ALL    0x0001 /* warning is activated when using -Wall */
#define FD_INVERT 0x0002 /* invert value before storing */

typedef struct FlagDef {
    uint16_t offset;
    uint16_t flags;
    const char *name;
} FlagDef;

static int no_flag(const char **pp)
{
    const char *p = *pp;
    if (*p != 'n' || *++p != 'o' || *++p != '-')
        return 0;
    *pp = p + 1;
    return 1;
}

ST_FUNC int set_flag(TCCState *s, const FlagDef *flags, const char *name)
{
    int value, ret;
    const FlagDef *p;
    const char *r;

    value = 1;
    r = name;
    if (no_flag(&r))
        value = 0;

    for (ret = -1, p = flags; p->name; ++p) {
        if (ret) {
            if (strcmp(r, p->name))
                continue;
        } else {
            if (0 == (p->flags & WD_ALL))
                continue;
        }
        if (p->offset) {
            *(int*)((char *)s + p->offset) =
                p->flags & FD_INVERT ? !value : value;
            if (ret)
                return 0;
        } else {
            ret = 0;
        }
    }
    return ret;
}

static int strstart(const char *val, const char **str)
{
    const char *p, *q;
    p = *str;
    q = val;
    while (*q) {
        if (*p != *q)
            return 0;
        p++;
        q++;
    }
    *str = p;
    return 1;
}

/* Like strstart, but automatically takes into account that ld options can
 * - start with double or single dash (e.g. '--soname' or '-soname')
 * - arguments can be given as separate or after '=' (e.g. '-Wl,-soname,x.so'
 *   or '-Wl,-soname=x.so')
 * you provide `val` always in 'option[=]' form (no leading -)
 */
static int link_option(const char *str, const char *val, const char **ptr)
{
    const char *p, *q;
    int ret;

    /* there should be 1 or 2 dashes */
    if (*str++ != '-')
        return 0;
    if (*str == '-')
        str++;

    /* then str & val should match (potentially up to '=') */
    p = str;
    q = val;

    ret = 1;
    if (q[0] == '?') {
        ++q;
        if (no_flag(&p))
            ret = -1;
    }

    while (*q != '\0' && *q != '=') {
        if (*p != *q)
            return 0;
        p++;
        q++;
    }

    /* '=' near eos means ',' or '=' is ok */
    if (*q == '=') {
        if (*p == 0)
            *ptr = p;
        if (*p != ',' && *p != '=')
            return 0;
        p++;
    } else if (*p) {
        return 0;
    }
    *ptr = p;
    return ret;
}

static const char *skip_linker_arg(const char **str)
{
    const char *s1 = *str;
    const char *s2 = strchr(s1, ',');
    *str = s2 ? s2++ : (s2 = s1 + strlen(s1));
    return s2;
}

static void copy_linker_arg(char **pp, const char *s, int sep)
{
    const char *q = s;
    char *p = *pp;
    int l = 0;
    if (p && sep)
        p[l = strlen(p)] = sep, ++l;
    skip_linker_arg(&q);
    pstrncpy(l + (*pp = tcc_realloc(p, q - s + l + 1)), s, q - s);
}

/* set linker options */
static int tcc_set_linker(TCCState *s, const char *option)
{
    while (*option) {

        const char *p = NULL;
        char *end = NULL;
        int ignoring = 0;
        int ret;

        if (link_option(option, "Bsymbolic", &p)) {
            s->symbolic = 1;
// JJX        } else if (link_option(option, "nostdlib", &p)) {
// JJX            s->nostdlib = 1;
        } else if (link_option(option, "fini=", &p)) {
            copy_linker_arg(&s->fini_symbol, p, 0);
            ignoring = 1;
        } else if (link_option(option, "image-base=", &p)
                || link_option(option, "Ttext=", &p)) {
            s->text_addr = strtoull(p, &end, 16);
            s->has_text_addr = 1;
        } else if (link_option(option, "init=", &p)) {
            copy_linker_arg(&s->init_symbol, p, 0);
            ignoring = 1;
        } else if (link_option(option, "oformat=", &p)) {
#if defined(TCC_TARGET_PE)
            if (strstart("pe-", &p)) {
#elif PTR_SIZE == 8
            if (strstart("elf64-", &p)) {
#else
            if (strstart("elf32-", &p)) {
#endif
                s->output_format = TCC_OUTPUT_FORMAT_ELF;
            } else if (!strcmp(p, "binary")) {
                s->output_format = TCC_OUTPUT_FORMAT_BINARY;
#ifdef TCC_TARGET_COFF
            } else if (!strcmp(p, "coff")) {
                s->output_format = TCC_OUTPUT_FORMAT_COFF;
#endif
            } else
                goto err;

        } else if (link_option(option, "as-needed", &p)) {
            ignoring = 1;
        } else if (link_option(option, "O", &p)) {
            ignoring = 1;
        } else if (link_option(option, "export-all-symbols", &p)) {
            s->rdynamic = 1;
        } else if (link_option(option, "rpath=", &p)) {
            copy_linker_arg(&s->rpath, p, ':');
        } else if (link_option(option, "enable-new-dtags", &p)) {
            s->enable_new_dtags = 1;
        } else if (link_option(option, "section-alignment=", &p)) {
            s->section_align = strtoul(p, &end, 16);
        } else if (link_option(option, "soname=", &p)) {
            copy_linker_arg(&s->soname, p, 0);
        } else if (ret = link_option(option, "?whole-archive", &p), ret) {
            s->no_alacarte_link = !( ret < 0 );
        } else if (p) {
            return 0;
        } else {
    err:
            tcc_error(-1, "unsupported linker option '%s'", option);
        }

        if( ignoring && s->warn_unsupported )  tcc_error(0, "unsupported linker option '%s'", option);

        option = skip_linker_arg(&p);
    }
    return 1;
}

typedef struct TCCOption {
    const char *name;
    uint16_t index;
    uint16_t flags;
} TCCOption;

enum {
    TCC_OPTION_HELP,
    TCC_OPTION_I,
    TCC_OPTION_D,
    TCC_OPTION_U,
    TCC_OPTION_L,
    TCC_OPTION_B,
    TCC_OPTION_l,
    TCC_OPTION_bench,
#ifdef CONFIG_TCC_BACKTRACE
    TCC_OPTION_bt,
#endif
#ifdef CONFIG_TCC_BCHECK
    TCC_OPTION_b,
#endif
#if defined CONFIG_TCC_GDEBUG
    TCC_OPTION_g,
#endif
    TCC_OPTION_c,
    TCC_OPTION_static,
    TCC_OPTION_soname,
    TCC_OPTION_r,
    TCC_OPTION_Wl,
    TCC_OPTION_Wp,
    TCC_OPTION_W,
    TCC_OPTION_O,
    TCC_OPTION_mfloat_abi,
    TCC_OPTION_f,
    TCC_OPTION_isystem,
    TCC_OPTION_iwithprefix,
    TCC_OPTION_include,
    // JJX    TCC_OPTION_nostdinc,
    // JJX    TCC_OPTION_nostdlib,
    TCC_OPTION_rdynamic,
    TCC_OPTION_param,
    TCC_OPTION_pthread,
    TCC_OPTION_run,
    TCC_OPTION_x,
};

#define TCC_OPTION_HAS_ARG 0x0001
#define TCC_OPTION_NOSEP   0x0002 /* cannot have space before option and arg */

static const TCCOption tcc_options[] = {
    { "h", TCC_OPTION_HELP, 0 },
    { "-help", TCC_OPTION_HELP, 0 },
    { "?", TCC_OPTION_HELP, 0 },
    { "I", TCC_OPTION_I, TCC_OPTION_HAS_ARG },
    { "D", TCC_OPTION_D, TCC_OPTION_HAS_ARG },
    { "U", TCC_OPTION_U, TCC_OPTION_HAS_ARG },
    { "L", TCC_OPTION_L, TCC_OPTION_HAS_ARG },
    { "B", TCC_OPTION_B, TCC_OPTION_HAS_ARG },
    { "l", TCC_OPTION_l, TCC_OPTION_HAS_ARG | TCC_OPTION_NOSEP },
    { "bench", TCC_OPTION_bench, 0 },
#ifdef CONFIG_TCC_BACKTRACE
    { "bt", TCC_OPTION_bt, TCC_OPTION_HAS_ARG },
#endif
#ifdef CONFIG_TCC_BCHECK
    { "b", TCC_OPTION_b, 0 },
#endif
#if defined CONFIG_TCC_GDEBUG
    { "g", TCC_OPTION_g, TCC_OPTION_HAS_ARG | TCC_OPTION_NOSEP },
#endif
    { "c", TCC_OPTION_c, 0 },
    { "static", TCC_OPTION_static, 0 },
    { "soname", TCC_OPTION_soname, TCC_OPTION_HAS_ARG },
    { "-param", TCC_OPTION_param, TCC_OPTION_HAS_ARG },
    { "pthread", TCC_OPTION_pthread, 0},
    { "run", TCC_OPTION_run, TCC_OPTION_HAS_ARG | TCC_OPTION_NOSEP },
    { "rdynamic", TCC_OPTION_rdynamic, 0 },
    { "r", TCC_OPTION_r, 0 },
    { "Wl,", TCC_OPTION_Wl, TCC_OPTION_HAS_ARG | TCC_OPTION_NOSEP },
    { "Wp,", TCC_OPTION_Wp, TCC_OPTION_HAS_ARG | TCC_OPTION_NOSEP },
    { "W", TCC_OPTION_W, TCC_OPTION_HAS_ARG | TCC_OPTION_NOSEP },
    { "O", TCC_OPTION_O, TCC_OPTION_HAS_ARG | TCC_OPTION_NOSEP },
#ifdef TCC_TARGET_ARM
    { "mfloat-abi", TCC_OPTION_mfloat_abi, TCC_OPTION_HAS_ARG },
#endif
    { "f", TCC_OPTION_f, TCC_OPTION_HAS_ARG | TCC_OPTION_NOSEP },
    { "isystem", TCC_OPTION_isystem, TCC_OPTION_HAS_ARG },
    { "include", TCC_OPTION_include, TCC_OPTION_HAS_ARG },
    // JJX    { "nostdinc", TCC_OPTION_nostdinc, 0 },
    // JJX    { "nostdlib", TCC_OPTION_nostdlib, 0 },
    { "x", TCC_OPTION_x, TCC_OPTION_HAS_ARG },
    { NULL, 0, 0 },
};

static const FlagDef options_W[] = {
    { 0, 0, "all" },
    { offsetof(TCCState, warn_unsupported), 0, "unsupported" },
    { offsetof(TCCState, warn_write_strings), 0, "write-strings" },
    { offsetof(TCCState, warn_error), 0, "error" },
    { offsetof(TCCState, warn_gcc_compat), 0, "gcc-compat" },
    { offsetof(TCCState, warn_implicit_function_declaration), WD_ALL,
      "implicit-function-declaration" },
    { 0, 0, NULL }
};

static const FlagDef options_f[] = {
    { offsetof(TCCState, char_is_unsigned), 0, "unsigned-char" },
    { offsetof(TCCState, char_is_unsigned), FD_INVERT, "signed-char" },
    { offsetof(TCCState, nocommon), FD_INVERT, "common" },
    { offsetof(TCCState, leading_underscore), 0, "leading-underscore" },
    { offsetof(TCCState, ms_extensions), 0, "ms-extensions" },
    { offsetof(TCCState, dollars_in_identifiers), 0, "dollars-in-identifiers" },
    { 0, 0, NULL }
};

// static const FlagDef options_m[] = { };

static void parse_option_D(TCCState *s1, const char *optarg)
{
    char *sym = tcc_strdup(optarg);
    char *value = strchr(sym, '=');
    if (value)
        *value++ = '\0';
    tcc_define_symbol(s1, sym, value);
    tcc_free(sym);
}

static void args_parser_add_file(TCCState *s, const char* filename, int filetype)
{
    struct filespec *f = tcc_malloc(sizeof *f + strlen(filename));
    f->type = filetype;
    f->no_alacarte = s->no_alacarte_link;
    strcpy(f->name, filename);
    dynarray_add(&s->files, &s->nb_files, f);
}

static int args_parser_make_argv(const char *r, int *argc, char ***argv)
{
    int ret = 0, q, c;
    CString str;
    for(;;) {
        while (c = (unsigned char)*r, c && c <= ' ')
	    ++r;
        if (c == 0)
            break;
        q = 0;
        cstr_new(&str);
        while (c = (unsigned char)*r, c) {
            ++r;
            if (c == '\\' && (*r == '"' || *r == '\\')) {
                c = *r++;
            } else if (c == '"') {
                q = !q;
                continue;
            } else if (q == 0 && c <= ' ') {
                break;
            }
            cstr_ccat(&str, c);
        }
        cstr_ccat(&str, 0);
        //printf("<%s>\n", str.data), fflush(stdout);
        dynarray_add(argv, argc, tcc_strdup(str.data));
        cstr_free(&str);
        ++ret;
    }
    return ret;
}

PUB_FUNC int tcc_parse_args(TCCState *s, int *pargc, char ***pargv, int optind)
{
    const TCCOption *popt;
    const char *optarg, *r;
    const char *run = NULL;
    int last_o = -1;
    int x;
    CString linker_arg; /* collect -Wl options */
    int arg_start = 0, noaction = optind;
    char **argv = *pargv;
    int argc = *pargc;

    cstr_new(&linker_arg);

    while( optind < argc ) {
        r = argv[optind];
        optind++;
reparse:
        if (r[0] != '-' || r[1] == '\0') {
            if (r[0] != '@') /* allow "tcc file(s) -run @ args ..." */
                args_parser_add_file(s, r, s->filetype);
            if (run) {
                tcc_set_options(s, run);
                arg_start = optind - 1;
                break;
            }
            continue;
        }

        /* find option in table */
        for(popt = tcc_options; ; ++popt) {
            const char *p1 = popt->name;
            const char *r1 = r + 1;
            if( p1 == NULL )  tcc_error(-1, "invalid option -- '%s'", r);
            if( !strstart( p1, &r1 ))  continue;
            optarg = r1;
            if (popt->flags & TCC_OPTION_HAS_ARG) {
                if (*r1 == '\0' && !(popt->flags & TCC_OPTION_NOSEP)) {
                    if (optind >= argc)
                arg_err:
                        tcc_error(-1, "argument to '%s' is missing", r);
                    optarg = argv[optind++];
                }
            } else if (*r1 != '\0')
                continue;
            break;
        }

        switch(popt->index) {
        case TCC_OPTION_HELP:
            return OPT_HELP;
        case TCC_OPTION_I:
            tcc_add_include_path(s, optarg);
            break;
        case TCC_OPTION_D:
            parse_option_D(s, optarg);
            break;
        case TCC_OPTION_U:
            tcc_undefine_symbol(s, optarg);
            break;
        case TCC_OPTION_L:
            tcc_add_library_path(s, optarg);
            break;
        case TCC_OPTION_B:
            /* set tcc utilities path (mainly for tcc development) */
            tcc_set_lib_path(s, optarg);
            break;
        case TCC_OPTION_l:
            args_parser_add_file(s, optarg, AFF_TYPE_LIB);
            s->nb_libraries++;
            break;
        case TCC_OPTION_pthread:
            parse_option_D(s, "_REENTRANT");
            s->option_pthread = 1;
            break;
        case TCC_OPTION_bench:
            s->do_bench = 1;
            break;
#ifdef CONFIG_TCC_BACKTRACE
        case TCC_OPTION_bt:
            tcc_set_num_callers(atoi(optarg));
            break;
#endif
#ifdef CONFIG_TCC_BCHECK
        case TCC_OPTION_b:
            s->do_bounds_check = 1;
            s->do_debug = 1;
            break;
#endif
#if defined CONFIG_TCC_GDEBUG
        case TCC_OPTION_g:
            s->do_debug = 1;
            break;
#endif
        case TCC_OPTION_c:
            x = TCC_OUTPUT_OBJ;
        set_output_type:
            if( s->output_type )
                tcc_error(0, "-%s: overriding compiler action already specified", popt->name);
            s->output_type = x;
            break;
        case TCC_OPTION_static:
            s->static_link = 1;
            break;
        case TCC_OPTION_soname:
            s->soname = tcc_strdup(optarg);
            break;
        case TCC_OPTION_r:
            /* generate a .o merging several output files */
            s->option_r = 1;
            x = TCC_OUTPUT_OBJ;
            goto set_output_type;
        case TCC_OPTION_isystem:
            tcc_add_sysinclude_path(s, optarg);
            break;
	case TCC_OPTION_include:
	    dynarray_add(&s->cmd_include_files,
			 &s->nb_cmd_include_files, tcc_strdup(optarg));
	    break;
// JJX        case TCC_OPTION_nostdinc:
// JJX            s->nostdinc = 1;
// JJX            break;
// JJX        case TCC_OPTION_nostdlib:
// JJX            s->nostdlib = 1;
// JJX            break;
        case TCC_OPTION_run:
#ifndef TCC_IS_NATIVE
            tcc_error(-1, "-run is not available in a cross compiler");
#endif
            run = optarg;
            x = TCC_OUTPUT_MEMORY;
            goto set_output_type;
        case TCC_OPTION_f:
            if (set_flag(s, options_f, optarg) < 0)
                goto unsupported_option;
            break;
#ifdef TCC_TARGET_ARM
        case TCC_OPTION_mfloat_abi:
            /* tcc doesn't support soft float yet */
            if (!strcmp(optarg, "softfp")) {
                s->float_abi = ARM_SOFTFP_FLOAT;
                tcc_undefine_symbol(s, "__ARM_PCS_VFP");
            } else if (!strcmp(optarg, "hard"))
                s->float_abi = ARM_HARD_FLOAT;
            else  tcc_error(-1, "unsupported float abi '%s'", optarg);
            break;
#endif
        case TCC_OPTION_W:
            if (set_flag(s, options_W, optarg) < 0)
                goto unsupported_option;
            break;
        case TCC_OPTION_rdynamic:
            s->rdynamic = 1;
            break;
        case TCC_OPTION_Wl:
            if (linker_arg.size)
                --linker_arg.size, cstr_ccat(&linker_arg, ',');
            cstr_cat(&linker_arg, optarg, 0);
            if (tcc_set_linker(s, linker_arg.data))
                cstr_free(&linker_arg);
            break;
	case TCC_OPTION_Wp:
	    r = optarg;
	    goto reparse;
        case TCC_OPTION_x:
            if (*optarg == 'c')
                s->filetype = AFF_TYPE_C;
            else if (*optarg == 'a')
                s->filetype = AFF_TYPE_ASMPP;
            else if (*optarg == 'n')
                s->filetype = AFF_TYPE_NONE;
            else  tcc_error(0, "unsupported language '%s'", optarg);
            break;
        case TCC_OPTION_O:
            last_o = atoi(optarg);
            break;
        default:
unsupported_option:
            if( s->warn_unsupported )  tcc_error(0, "unsupported option '%s'", r);
            break;
        }
    }
    if (last_o > 0) tcc_define_symbol(s, "__OPTIMIZE__", NULL);
    if (linker_arg.size) {
        r = linker_arg.data;
        goto arg_err;
    }
    *pargc = argc - arg_start;
    *pargv = argv + arg_start;
    if (optind != noaction) return 0;
    return OPT_HELP;
}

LIBTCCAPI void tcc_set_options(TCCState *s, const char *r)
{
    char **argv = NULL;
    int argc = 0;
    args_parser_make_argv(r, &argc, &argv);
    tcc_parse_args(s, &argc, &argv, 0);
    dynarray_reset(&argv, &argc);
}


/**  end of libtcc.c  **/

#endif  /**  #if ONE_SOURCE  **/
















#include "jitcc.h"









// JJX  Old:  JITCC_API int  Main( int argc0, char **argv0 ) {
JITCC_API int jitcc( const char *inputfile, const char *outputfile, FILE *dbgfh ) {
////  Eg.:                      ~http.path,           ~memfilename,       ~NULL
////  if OK                            return         -1
////  if ERROR here and no file-output return     x < -1
////  if ERROR      and    file-output return fdesc > -1

    TCCState * s;
    // char * se_path;  // JJX  not needed now
    struct timeval  tv;
    unsigned  start_time, end_time;
    int  ret, stjmpret;
    // int  opt, n, t;
    // const char * first_file;
    // int  argc; char **argv;

    jjglob_newdone =  0;
    jjglob_retval  = -1;
    jmp_var        =  0;
    jjglob_dbgfh   = NULL;
    tcc_state      = NULL;
    file           = NULL;

    s = NULL;
    start_time = end_time = (unsigned int) 0;
    ret = 0;
    // n = 0; t = 0;

    if( !inputfile )   return -31;
    if( !outputfile )  return -32;
    if( dbgfh )  jjglob_dbgfh = dbgfh;  // an open file handle

    stjmpret = setjmp( err_jmp_buf1 );
    if( 0 != stjmpret ) {   // longjmp-d here from tcc_error()
       jmp_var = 3;
       goto _error_to_main;
    }
    jmp_var = 1;

    s = tcc_new();  // first func that can fail w tcc_error() , so placing setjmp() before it
    if( NULL == s )  return -33;
    jjglob_newdone = 1;

    s->outfile = outputfile;
    if( dbgfh ) {
      s->verbose  = 1;
      s->do_bench = 1;
      s->do_warn  = 1;
    }
    s->output_type = TCC_OUTPUT_DLL;

// redo:
    // argc = argc0, argv = argv0;
    // s = tcc_new();
    // opt = tcc_parse_args( s, &argc, &argv, 1 );

    // if( !( n|t )) {
       // if( OPT_HELP == opt )  return 1;
       // n = s->nb_files;
       // if( !n )  tcc_error(-1, "no input files\n" );
       // if( TCC_OUTPUT_OBJ == s->output_type && !s->option_r ) {
          // if( s->nb_libraries )  tcc_error(-1, "cannot specify libraries with -c" );
          // if( n > 1 && s->outfile )  tcc_error(-1, "cannot specify output file with -c many files" );
       // }
       // else {
          // if( s->option_pthread )  tcc_set_options( s, "-lpthread" );
       // }
       if( s->do_bench ) {
          gettimeofday( &tv, NULL );
          start_time = (unsigned)( tv.tv_sec*1000 + (tv.tv_usec+500)/1000 );
       }
    // }

    {  // JJX  it was:   set_environment( s );
       // JJX  !  These are NOT specified in the Server !
       /**  -isystem (paths) == 'tcc_add_sysinclude_path'  **/
//     se_path = getenv( "C_INCLUDE_PATH" ); if( NULL != se_path ) tcc_add_sysinclude_path( s, se_path );
//     se_path = getenv( "CPATH"          ); if( NULL != se_path ) tcc_add_include_path(    s, se_path );
//     se_path = getenv( "LIBRARY_PATH"   ); if( NULL != se_path ) tcc_add_library_path(    s, se_path );
       //
       // JJXS   for TinyCore SERVER (checked w resident tcc) :
       // JJXS   include:    /usr/local/lib/tcc/include ; /usr/local/include /usr/include
       // JJXS   libraries:  /usr/lib ; /lib ; /usr/local/lib
       // JJXS   install:    /usr/local/lib/tcc   => libtcc1.a + include/ *.h
       // JJXS   libtcc1:    /usr/local/lib/tcc/libtcc1.a
       // JJXS   crt:        /usr/lib
       // JJXS   elfinterp:  /lib64/ld-linux-x86-64.so.2
    }
    // if( !s->output_type )  s->output_type = TCC_OUTPUT_DLL;


///// JJXXXXXX   These could be hard-coded OR get them ready through fork() !?
    {  // JJX  (formerly:)  tcc_set_output_type(s, s->output_type);
       // if( TCC_OUTPUT_OBJ == s->output_type ) s->output_format = TCC_OUTPUT_FORMAT_ELF;
       if( s->char_is_unsigned ) tcc_define_symbol( s, "__CHAR_UNSIGNED__", NULL );
       // JJX  disabled for now:  if( !s->nostdinc )
          tcc_add_sysinclude_path( s, CONFIG_TCC_SYSINCLUDEPATHS );  // defalt include paths
#ifdef CONFIG_TCC_BCHECK
       if( s->do_bounds_check ) {
          tccelf_bounds_new( s );
          tcc_define_symbol( s, "__BOUNDS_CHECKING_ON", NULL );
       }
#endif
#if defined CONFIG_TCC_GDEBUG
       if( s->do_debug )  tccelf_stab_new( s );  // add debug sections
#endif
       (void) tcc_add_library_path( s, CONFIG_TCC_LIBPATHS );
       tcc_split_path( s, &s->crt_paths, &s->nb_crt_paths, CONFIG_TCC_CRTPREFIX );  // paths for crt objects
       if( TCC_OUTPUT_DLL == s->output_type /* && !s->nostdlib */ )  (void) tcc_add_crt( s, "crti.o" );
    }


    /* compile or add each files or library */
    // for( first_file = NULL, ret = 0; ; ) {
    // ret = 0;
       // struct filespec *f = s->files[s->nb_files - n];
       // s->filetype = f->type;
       // s->no_alacarte_link = f->no_alacarte;   // s->no_alacarte_link = 0;
       // if( AFF_TYPE_LIB == f->type ) { if( 0 > tcc_add_library_err( s, f->name )) ret = 1; }
       // else {
          // if( 1 == s->verbose ) printf( "-> %s\n", f->name );
          if( s->verbose )  (void) fprintf( jjglob_dbgfh, " JJVERBOSE:  -> %s\n", inputfile );
          // if( !first_file ) first_file = f->name;
          // if( 0 > tcc_add_file( s, f->name )) ret = 1;
          ret = tcc_add_file( s, inputfile );
          if( 0 > ret ) {  // ERROR
             if( -1 == jjglob_retval || -2 == jjglob_retval )  jjglob_retval = -34;
          }
          else  ret = 0;
       // }
       s->filetype = 0;  // JJX  important to have it
       // s->no_alacarte_link = 0;
       // if( 0 == --n || ret || ( TCC_OUTPUT_OBJ == s->output_type && !s->option_r ))  break;
    // }

    if( !ret ) {
       // if( TCC_OUTPUT_MEMORY == s->output_type ) {
#ifdef TCC_IS_NATIVE
          // ret = tcc_run( s, argc, argv );
#endif
       // }
       // else {
          if(( tcc_output_file( s, s->outfile ))) {   // JJX  this can be inlined
             if( -1 == jjglob_retval || -2 == jjglob_retval )  jjglob_retval = -35;
          }
       // }
    }

    // if( s->do_bench && !( n|t|ret )) {
    if( s->do_bench && !ret ) {
       gettimeofday( &tv, NULL );
       end_time = ((unsigned)( tv.tv_sec*1000 + (tv.tv_usec+500)/1000 )) - start_time;
       if( 1 > end_time    )    end_time = 1;
       if( 1 > total_bytes ) total_bytes = 1;
       (void) fprintf( jjglob_dbgfh, " JJTIMER:  * %d idents, %d lines, %d bytes\n"
                                     " JJTIMER:  * %0.3f s, %u lines/s, %0.1f MB/s\n",
                                     tok_ident - TOK_IDENT, total_lines, total_bytes,
                                     (double)( end_time/1000 ),
                                     (unsigned)( total_lines*1000/end_time ),
                                     (double)( total_bytes/1000/end_time ));
#ifdef MEM_DEBUG
       (void) fprintf( jjglob_dbgfh, " JJTIMER:  * %d bytes memory used.\n", mem_max_size );
#endif
    }

_error_to_main:  ;

    tcc_delete( s );
    // if( !ret && n ) goto redo;  // compile more files with -c

    (void) fflush( NULL );  // flushes all open output streams
       // JJX  fflush() what you need to:    !  outfile / jjglob_dbgfh
       // if( jjglob_dbgfh )  (void) fflush( jjglob_dbgfh );

    // JJX  One may want to do rewind() here, or one may do it
    //      in the calling process/func after the return:
    // (void) rewind( jjglob_dbgfh );

  return  jjglob_retval;
}

