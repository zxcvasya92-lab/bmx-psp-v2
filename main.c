// BMX Streets Lite 3D - 3D BMX для PSP (pspdev / PSPSDK, графика через GU)
//
// УПРАВЛЕНИЕ
//  Земля:
//    Левый стик влево/вправо . руль (повернуть руль)
//    Долбёжка X ............. разгон
//    Стик вниз -> вверх ..... банихоп (+ держать X = высокий банихоп)
//    Крестовина лево/право .. разворот на 180 (так можно поехать фейки)
//    Фейки + Треугольник .... руль на 90 градусов, слайд
//       стик влево/вправо в слайде = выход из слайда лицом вперёд
//  Воздух:
//    L (держать) ............ поджать ноги (байк чуть выше)
//    R (держать) ............ руки (отпустить руль)
//    L + X .................. кренкфлип
//    L + O .................. вип
//    стик вверх + L + O ..... футджем вип
//    R + O .................. бар
//    стик вниз + R + O ...... чикенбар
//    R + X .................. (пока не назначено)
//    Крестовина лево/право .. 180, 360 ... (каждое нажатие = +180)
//    Крестовина вверх/вниз .. фронтфлип / бэкфлип
//  START ...................... справка
//
// Все модели (байк, райдер, рампы, здания) построены кодом из примитивов.
// Место для подключения своих моделей: draw_rider() и draw_ramp().
#include <pspkernel.h>
#include <pspdisplay.h>
#include <pspctrl.h>
#include <pspdebug.h>
#include <pspgu.h>
#include <pspgum.h>
#include <math.h>
#include <stdio.h>
#include <string.h>
#include <stdlib.h>

PSP_MODULE_INFO("BMX Streets Lite 3D", 0, 1, 0);
PSP_MAIN_THREAD_ATTR(THREAD_ATTR_USER | THREAD_ATTR_VFPU);

#define BUF_W 512
#define SCR_W 480
#define SCR_H 272
#define DT (1.0f / 60.0f)
#define G 14.0f
#define PI 3.1415927f
#define PI2 6.2831853f
#define STEER_SIGN 1.0f /* если руль перепутан влево/вправо - поставьте -1.0f */
#define RGB(r, g, b) (0xFF000000u | ((b) << 16) | ((g) << 8) | (r))
#define SKY RGB(125, 185, 240)

static unsigned int __attribute__((aligned(16))) list[262144];

static int exit_callback(int a, int b, void *c) { sceKernelExitGame(); return 0; }
static int cb_thread(SceSize args, void *argp)
{
    int id = sceKernelCreateCallback("exit", exit_callback, NULL);
    sceKernelRegisterExitCallback(id);
    sceKernelSleepThreadCB();
    return 0;
}
static void setup_callbacks(void)
{
    int t = sceKernelCreateThread("cb", cb_thread, 0x11, 0xFA0, 0, 0);
    if (t >= 0) sceKernelStartThread(t, 0, 0);
}

/* ================= математика ================= */
typedef struct { float x, y, z; } V3;
typedef struct { float r[9], t[3]; } Mat;

static V3 v3(float x, float y, float z) { V3 p = {x, y, z}; return p; }
static Mat mId(void) { Mat m = {{1, 0, 0, 0, 1, 0, 0, 0, 1}, {0, 0, 0}}; return m; }
static Mat mT(float x, float y, float z) { Mat m = mId(); m.t[0] = x; m.t[1] = y; m.t[2] = z; return m; }
static Mat mRY(float a) { float c = cosf(a), s = sinf(a); Mat m = {{c, 0, s, 0, 1, 0, -s, 0, c}, {0, 0, 0}}; return m; }
static Mat mRX(float a) { float c = cosf(a), s = sinf(a); Mat m = {{1, 0, 0, 0, c, s, 0, -s, c}, {0, 0, 0}}; return m; } /* +a = нос вверх */
static Mat mRZ(float a) { float c = cosf(a), s = sinf(a); Mat m = {{c, -s, 0, s, c, 0, 0, 0, 1}, {0, 0, 0}}; return m; }
static Mat mMul(Mat a, Mat b)
{
    Mat o;
    for (int i = 0; i < 3; i++) {
        for (int j = 0; j < 3; j++)
            o.r[i * 3 + j] = a.r[i * 3] * b.r[j] + a.r[i * 3 + 1] * b.r[3 + j] + a.r[i * 3 + 2] * b.r[6 + j];
        o.t[i] = a.r[i * 3] * b.t[0] + a.r[i * 3 + 1] * b.t[1] + a.r[i * 3 + 2] * b.t[2] + a.t[i];
    }
    return o;
}
static V3 mPt(const Mat *m, float x, float y, float z)
{
    V3 p = {m->r[0] * x + m->r[1] * y + m->r[2] * z + m->t[0],
            m->r[3] * x + m->r[4] * y + m->r[5] * z + m->t[1],
            m->r[6] * x + m->r[7] * y + m->r[8] * z + m->t[2]};
    return p;
}
static V3 lerp3(V3 a, V3 b, float t) { return v3(a.x + (b.x - a.x) * t, a.y + (b.y - a.y) * t, a.z + (b.z - a.z) * t); }
static float clampf(float v, float a, float b) { return v < a ? a : (v > b ? b : v); }
static float approach(float c, float t, float r)
{
    if (c < t) { c += r; if (c > t) c = t; }
    else if (c > t) { c -= r; if (c < t) c = t; }
    return c;
}

/* ================= геометрия (CPU -> GU) ================= */
typedef struct { unsigned int c; float x, y, z; } Vtx;
#define MAXV 20000
static Vtx vbuf[MAXV] __attribute__((aligned(16)));
static int nv = 0;

static void tri(V3 a, V3 b, V3 c, unsigned col)
{
    if (nv + 3 > MAXV) return;
    float ux = b.x - a.x, uy = b.y - a.y, uz = b.z - a.z;
    float vx = c.x - a.x, vy = c.y - a.y, vz = c.z - a.z;
    float nx = uy * vz - uz * vy, ny = uz * vx - ux * vz, nz = ux * vy - uy * vx;
    float l = sqrtf(nx * nx + ny * ny + nz * nz);
    float sh = 0.6f;
    if (l > 1e-6f) sh = 0.45f + 0.55f * fabsf((nx * 0.40f + ny * 0.80f + nz * 0.35f) / l);
    if (sh > 1) sh = 1;
    unsigned r = (unsigned)((col & 255) * sh), g = (unsigned)(((col >> 8) & 255) * sh), b2 = (unsigned)(((col >> 16) & 255) * sh);
    unsigned cc = 0xFF000000u | (b2 << 16) | (g << 8) | r;
    vbuf[nv].c = cc; vbuf[nv].x = a.x; vbuf[nv].y = a.y; vbuf[nv].z = a.z; nv++;
    vbuf[nv].c = cc; vbuf[nv].x = b.x; vbuf[nv].y = b.y; vbuf[nv].z = b.z; nv++;
    vbuf[nv].c = cc; vbuf[nv].x = c.x; vbuf[nv].y = c.y; vbuf[nv].z = c.z; nv++;
}
static void quad(V3 a, V3 b, V3 c, V3 d, unsigned col) { tri(a, b, c, col); tri(a, c, d, col); }

/* "труба" (прямоугольный брусок) между двумя точками мира */
static void limb(V3 a, V3 b, float t, unsigned col)
{
    float dx = b.x - a.x, dy = b.y - a.y, dz = b.z - a.z;
    float l = sqrtf(dx * dx + dy * dy + dz * dz);
    if (l < 1e-4f) return;
    dx /= l; dy /= l; dz /= l;
    float rx = 0, ry = 1, rz = 0;
    if (fabsf(dy) > 0.9f) { rx = 1; ry = 0; }
    float ux = dy * rz - dz * ry, uy = dz * rx - dx * rz, uz = dx * ry - dy * rx;
    float ul = sqrtf(ux * ux + uy * uy + uz * uz);
    ux *= t / ul; uy *= t / ul; uz *= t / ul;
    float vx = dy * uz - dz * uy, vy = dz * ux - dx * uz, vz = dx * uy - dy * ux;
    static const float s1[4] = {1, 1, -1, -1}, s2[4] = {1, -1, -1, 1};
    V3 c[8];
    for (int i = 0; i < 4; i++) {
        c[i] = v3(a.x + ux * s1[i] + vx * s2[i], a.y + uy * s1[i] + vy * s2[i], a.z + uz * s1[i] + vz * s2[i]);
        c[i + 4] = v3(b.x + ux * s1[i] + vx * s2[i], b.y + uy * s1[i] + vy * s2[i], b.z + uz * s1[i] + vz * s2[i]);
    }
    for (int i = 0; i < 4; i++) { int j = (i + 1) & 3; quad(c[i], c[j], c[j + 4], c[i + 4], col); }
    quad(c[0], c[1], c[2], c[3], col);
    quad(c[4], c[5], c[6], c[7], col);
}

/* ================= уровень ================= */
#define RW 3.5f
typedef struct { int n; float x[5], h[5]; } Prof;
static const Prof prof[4] = {
    {3, {0, 5, 5}, {0, 1.1f, 0}},                 /* кикер */
    {4, {0, 4, 7, 11}, {0, 0.9f, 0.9f, 0}},       /* фанбокс */
    {3, {0, 8, 8}, {0, 2.0f, 0}},                 /* большой кикер */
    {3, {0, 3, 6}, {0, 0.5f, 0}}                  /* роллер */
};
typedef struct { int t; float cx, cz, yaw; } Ramp;
static const Ramp ramps[] = {
    {0, 0, 14, 0},          {1, -14, 30, 0},       {2, 14, 36, 0},
    {3, 0, 52, 0},          {0, 28, 4, 1.5708f},   {1, -34, 6, -1.5708f},
    {2, -8, -30, 3.1416f},  {3, 22, -22, 0.8f},    {1, 40, 40, 2.4f}
};
#define NRAMPS ((int)(sizeof(ramps) / sizeof(ramps[0])))
#define LIMIT 85.0f

static float rampH(const Ramp *r, float x, float z)
{
    float dx = x - r->cx, dz = z - r->cz;
    float s = sinf(r->yaw), c = cosf(r->yaw);
    float lx = dx * s + dz * c, lz = dx * c - dz * s;
    if (fabsf(lz) > RW / 2) return 0;
    const Prof *p = &prof[r->t];
    for (int i = 0; i < p->n - 1; i++)
        if (p->x[i + 1] > p->x[i] && lx >= p->x[i] && lx <= p->x[i + 1])
            return p->h[i] + (p->h[i + 1] - p->h[i]) * (lx - p->x[i]) / (p->x[i + 1] - p->x[i]);
    return 0;
}
static float H(float x, float z)
{
    float h = 0;
    for (int i = 0; i < NRAMPS; i++) {
        float v = rampH(&ramps[i], x, z);
        if (v > h) h = v;
    }
    return h;
}
static float slopeAlong(float x, float z, float dx, float dz)
{
    return clampf((H(x + dx * 0.4f, z + dz * 0.4f) - H(x - dx * 0.4f, z - dz * 0.4f)) / 0.8f, -1.2f, 1.2f);
}

static V3 rpt(const Ramp *r, float lx, float lz, float h)
{
    float s = sinf(r->yaw), c = cosf(r->yaw);
    return v3(r->cx + lx * s + lz * c, h, r->cz + lx * c - lz * s);
}
static void draw_ramp(const Ramp *r)
{
    const Prof *p = &prof[r->t];
    float hw = RW / 2;
    for (int i = 0; i < p->n - 1; i++) {
        unsigned col = p->x[i + 1] > p->x[i] ? RGB(205, 170, 95) : RGB(150, 120, 70);
        quad(rpt(r, p->x[i], -hw, p->h[i]), rpt(r, p->x[i + 1], -hw, p->h[i + 1]),
             rpt(r, p->x[i + 1], hw, p->h[i + 1]), rpt(r, p->x[i], hw, p->h[i]), col);
    }
    for (int i = 1; i < p->n - 1; i++) {
        tri(rpt(r, p->x[0], -hw, p->h[0]), rpt(r, p->x[i], -hw, p->h[i]), rpt(r, p->x[i + 1], -hw, p->h[i + 1]), RGB(150, 120, 70));
        tri(rpt(r, p->x[0], hw, p->h[0]), rpt(r, p->x[i], hw, p->h[i]), rpt(r, p->x[i + 1], hw, p->h[i + 1]), RGB(150, 120, 70));
    }
}

static void abox(float cx, float cz, float hx, float hz, float h, unsigned col)
{
    V3 a0 = v3(cx - hx, 0, cz - hz), a1 = v3(cx + hx, 0, cz - hz), a2 = v3(cx + hx, 0, cz + hz), a3 = v3(cx - hx, 0, cz + hz);
    V3 b0 = v3(cx - hx, h, cz - hz), b1 = v3(cx + hx, h, cz - hz), b2 = v3(cx + hx, h, cz + hz), b3 = v3(cx - hx, h, cz + hz);
    quad(b0, b1, b2, b3, col);
    quad(a0, a1, b1, b0, col); quad(a1, a2, b2, b1, col);
    quad(a2, a3, b3, b2, col); quad(a3, a0, b0, b3, col);
}

#define TILE 6.0f
static void draw_ground(float px, float pz)
{
    int ti = (int)floorf(px / TILE), tj = (int)floorf(pz / TILE);
    for (int i = -12; i < 12; i++)
        for (int j = -12; j < 12; j++) {
            int a = ti + i, b = tj + j;
            float x0 = a * TILE, z0 = b * TILE;
            unsigned col = ((a + b) & 1) ? RGB(118, 118, 124) : RGB(98, 98, 104);
            quad(v3(x0, 0, z0), v3(x0 + TILE, 0, z0), v3(x0 + TILE, 0, z0 + TILE), v3(x0, 0, z0 + TILE), col);
        }
}

static void draw_buildings(void)
{
    for (int i = -4; i <= 4; i++) {
        unsigned c1 = RGB(120 + (abs(i) * 23) % 60, 110 + (abs(i) * 37) % 50, 130);
        unsigned c2 = RGB(140, 120 + (abs(i) * 29) % 60, 110 + (abs(i) * 11) % 40);
        float h = 10 + ((abs(i) * 7) % 5) * 4;
        abox(i * 22.0f, 100, 8, 6, h, c1);
        abox(i * 22.0f, -100, 8, 6, h + 2, c2);
        abox(100, i * 22.0f, 6, 8, h + 1, c2);
        abox(-100, i * 22.0f, 6, 8, h - 1, c1);
    }
}

/* ================= состояние игры ================= */
enum { T_NONE, T_WHIP, T_CRANK, T_FOOTJAM, T_BAR, T_CHICKEN };
static const char *tname[] = {"", "WHIP", "CRANKFLIP", "FOOTJAM WHIP", "BAR", "CHICKENBAR"};
static const int tpts[] = {0, 100, 130, 150, 120, 180};
static const float tdur[] = {0, 0.5f, 0.55f, 0.5f, 0.45f, 0.5f};

static float px = 0, py = 0, pz = 0, sp = 0, vy = 0, hdg = 0;
static float pitchBase = 0, flipCur = 0, flipTgt = 0;
static float yawCur = 0, yawTgt = 0, yawTakeoff = 0;
static float tuck = 0, armUp = 0, lean = 0, pivH = 0, slideVis = 0;
static float wheelRot = 0, crankPh = 0;
static int air = 0, slide = 0;
static int pending = 0, score = 0, combo = 0;
static float trickT = 0, trickDur = 0, comboT = 0, crashT = 0, msgT = 0;
static float downT = 0, camAng = 0, camY = 3;
static int downHeld = 0, trickType = 0;
static const char *lastName = "";
static char msg[64] = "";

static int facing(void) { return cosf(yawTgt) > 0 ? 1 : -1; }

static void bank(int total, const char *name)
{
    combo = comboT > 0 ? combo + 1 : 1;
    score += total * combo;
    comboT = 3.0f;
    snprintf(msg, sizeof(msg), "%s+%d x%d", name, total, combo);
    msgT = 1.6f;
}

static void crash_now(void)
{
    crashT = 1.2f; pending = 0; combo = 0; comboT = 0; sp = 0; vy = 0;
    slide = 0; air = 0; trickT = 0;
    snprintf(msg, sizeof(msg), "CRASH!"); msgT = 1.2f;
}

static void respawn(void)
{
    if (H(px, pz) > 0.05f) { px = 0; pz = 0; hdg = 0; }
    py = H(px, pz);
    sp = vy = 0; air = 0; slide = 0; trickT = 0; pending = 0;
    pitchBase = flipCur = flipTgt = 0;
    yawCur = yawTgt = 0; tuck = armUp = lean = pivH = slideVis = 0;
}

static void takeoff(float vyInit)
{
    air = 1; vy = vyInit; flipCur = flipTgt = 0; yawTakeoff = yawTgt; trickT = 0; pending = 0;
}

static void end_slide(int out)
{
    slide = 0;
    if (out) { yawTgt += PI; bank(300, "FAKIE SLIDE OUT "); }
    else bank(100, "SLIDE ");
}

static void start_trick(int t) { trickType = t; trickDur = trickT = tdur[t]; }

static void do_land(float gh, float sl)
{
    float tgt = atanf(sl);
    float d = remainderf(pitchBase - tgt, PI2);
    float fe = fabsf(flipTgt - flipCur), ye = fabsf(yawTgt - yawCur);
    py = gh; air = 0; vy = 0;
    if (trickT > 0 || fabsf(d) > 0.75f || fe > 0.7f || ye > 0.9f) { crash_now(); return; }
    int flips = (int)(fabsf(flipTgt) / PI2 + 0.5f);
    int spins = (int)(fabsf(yawTgt - yawTakeoff) / PI + 0.5f);
    int total = pending + flips * 300 + spins * 150;
    if (total > 0) {
        char nm[48]; int o = 0; nm[0] = 0;
        if (pending > 0) o += snprintf(nm + o, sizeof(nm) - o, "%s ", lastName);
        if (flips) o += snprintf(nm + o, sizeof(nm) - o, "FLIP ");
        if (spins && o < (int)sizeof(nm) - 8) snprintf(nm + o, sizeof(nm) - o, "%d ", spins * 180);
        bank(total, nm);
    }
    pending = 0;
    pitchBase = tgt; flipCur = flipTgt = 0;
    yawTgt = (((int)lroundf(yawTgt / PI)) & 1) ? PI : 0;
    yawCur = yawTgt;
}

static void update(unsigned btn, unsigned pressed, int lxr, int lyr)
{
    float sx = (lxr - 128) / 128.0f;
    if (fabsf(sx) < 0.18f) sx = 0;
    int stickUp = lyr < 64, stickDown = lyr > 192, stickL = lxr < 64, stickR = lxr > 192;
    int L = (btn & PSP_CTRL_LTRIGGER) != 0, R = (btn & PSP_CTRL_RTRIGGER) != 0;

    if (msgT > 0) msgT -= DT;
    yawCur = approach(yawCur, yawTgt, 11.0f * DT);
    flipCur = approach(flipCur, flipTgt, 9.0f * DT);
    tuck = approach(tuck, (air && L) ? 1.0f : 0.0f, 10.0f * DT);
    armUp = approach(armUp, (R && (air || trickT > 0)) ? 1.0f : 0.0f, 10.0f * DT);
    slideVis = approach(slideVis, slide ? PI / 2 : 0, 9.0f * DT);
    pivH = approach(pivH, air ? 0.8f : 0.0f, 6.0f * DT);

    if (crashT > 0) {
        pitchBase += 7 * DT;
        float g0 = H(px, pz);
        vy -= G * DT; py += vy * DT;
        if (py < g0) { py = g0; vy = 0; }
        crashT -= DT;
        if (crashT <= 0) respawn();
        return;
    }

    wheelRot += sp * DT / 0.33f;
    if (!air) crankPh += sp * DT * 1.6f;
    float dx = sinf(hdg), dz = cosf(hdg);

    if (!air) {
        int f = facing();
        int fakie = (f < 0 && sp > 0.5f);
        float sl = slopeAlong(px, pz, dx, dz);

        if (slide) {
            sp -= 5.0f * DT * (sp > 0 ? 1 : -1);
            if (fabsf(sp) < 0.4f) { sp = 0; end_slide(0); }
            else if (stickL || stickR) end_slide(1);
            else if (!(btn & PSP_CTRL_TRIANGLE)) end_slide(0);
        } else {
            hdg -= STEER_SIGN * sx * 1.9f * DT * clampf(fabsf(sp) / 3.0f, 0.3f, 1.0f);
            if (pressed & (PSP_CTRL_LEFT | PSP_CTRL_RIGHT)) yawTgt += PI;
            if (pressed & PSP_CTRL_CROSS) sp += 0.8f;
            if ((pressed & PSP_CTRL_TRIANGLE) && fakie && sp > 1.0f) slide = 1;
        }
        lean = approach(lean, slide ? 0 : sx * STEER_SIGN * 0.35f * clampf(fabsf(sp) / 5.0f, 0, 1), 6.0f * DT);
        sp -= sp * 0.4f * DT;
        sp -= G * sl / (1 + sl * sl) * DT;
        sp = clampf(sp, -3, 9);
        if (comboT > 0) { comboT -= DT; if (comboT <= 0) combo = 0; }

        /* банихоп: стик вниз -> вверх */
        if (stickDown) { downHeld = 1; downT = 0.45f; }
        else if (downHeld) { downT -= DT; if (downT <= 0) downHeld = 0; }

        dx = sinf(hdg); dz = cosf(hdg);
        if (downHeld && stickUp && !slide) {
            float hop = (btn & PSP_CTRL_CROSS) ? 6.2f : 4.0f;
            downHeld = 0;
            takeoff(sp * sl + hop);
            px += dx * sp * DT; pz += dz * sp * DT; py += vy * DT;
        } else {
            float nx = clampf(px + dx * sp * DT, -LIMIT, LIMIT);
            float nz = clampf(pz + dz * sp * DT, -LIMIT, LIMIT);
            float npy = py + sp * sl * DT;
            float gh = H(nx, nz);
            if (gh - npy > 0.4f && fabsf(sp) > 0.3f) {
                crash_now();               /* врезались в стенку рампы */
            } else {
                px = nx; pz = nz;
                if (npy > gh + 0.12f) { py = npy; takeoff(sp * sl); }
                else { py = gh; pitchBase = atanf(sl); }
            }
        }
    } else {
        int f = facing(); (void)f;
        float ox = px, oz = pz, oy = py;
        vy -= G * DT;
        px = clampf(px + dx * sp * DT, -LIMIT, LIMIT);
        pz = clampf(pz + dz * sp * DT, -LIMIT, LIMIT);
        py += vy * DT;
        lean = approach(lean, 0, 6.0f * DT);

        float tr = clampf(atan2f(vy, fmaxf(sp, 1.0f)), -1.0f, 1.0f);
        pitchBase = approach(pitchBase, tr, 2.5f * DT);

        /* крестовина: развороты и флипы */
        if (pressed & PSP_CTRL_LEFT) yawTgt -= PI;
        if (pressed & PSP_CTRL_RIGHT) yawTgt += PI;
        if (pressed & PSP_CTRL_UP) flipTgt -= PI2;     /* фронтфлип */
        if (pressed & PSP_CTRL_DOWN) flipTgt += PI2;   /* бэкфлип */

        /* трюки */
        if (trickT <= 0) {
            if (pressed & PSP_CTRL_CIRCLE) {
                if (L && stickUp) start_trick(T_FOOTJAM);
                else if (L) start_trick(T_WHIP);
                else if (R && stickDown) start_trick(T_CHICKEN);
                else if (R) start_trick(T_BAR);
            } else if (pressed & PSP_CTRL_CROSS) {
                if (L) start_trick(T_CRANK);
                /* R + X: пока не назначено */
            }
        } else {
            trickT -= DT;
            if (trickT <= 0) {
                trickT = 0;
                pending += tpts[trickType];
                lastName = tname[trickType];
                snprintf(msg, sizeof(msg), "%s", lastName); msgT = 0.8f;
            }
        }

        float gh = H(px, pz);
        if (py < gh) {
            if (gh - py > 0.45f) { px = ox; pz = oz; py = oy; crash_now(); }
            else do_land(gh, slopeAlong(px, pz, dx, dz));
        }
    }
    camAng += remainderf(hdg - camAng, PI2) * 3.0f * DT;
}

/* ================= рисование райдера =================
   Здесь подключаются свои модели: bike/rider матрицы уже посчитаны. */
static void wheel(const Mat *m, float cz, float r, float spin)
{
    const int N = 14;
    float cy = 0.33f, hw = 0.03f;
    unsigned tire = RGB(35, 35, 40), cap = RGB(70, 70, 80);
    V3 pL[14], pR[14];
    for (int k = 0; k < N; k++) {
        float a = k * PI2 / N;
        pL[k] = mPt(m, hw, cy + r * cosf(a), cz + r * sinf(a));
        pR[k] = mPt(m, -hw, cy + r * cosf(a), cz + r * sinf(a));
    }
    for (int k = 0; k < N; k++) {
        int j = (k + 1) % N;
        quad(pL[k], pL[j], pR[j], pR[k], tire);
    }
    for (int k = 1; k < N - 1; k++) {
        tri(pL[0], pL[k], pL[k + 1], cap);
        tri(pR[0], pR[k], pR[k + 1], cap);
    }
    V3 s0 = mPt(m, hw + 0.005f, cy + r * 0.9f * cosf(spin), cz + r * 0.9f * sinf(spin));
    V3 s1 = mPt(m, hw + 0.005f, cy - r * 0.9f * cosf(spin), cz - r * 0.9f * sinf(spin));
    limb(s0, s1, 0.012f, RGB(220, 220, 230));
}

static void draw_rider(void)
{
    float c = cosf(yawCur);
    float pitch = pitchBase * c + flipCur;
    float roll = lean * c;
    float prog = trickT > 0 ? 1.0f - trickT / trickDur : 0;
    int tt = trickT > 0 ? trickType : T_NONE;
    float bikeYaw = slideVis, bikePitch = 0, barPh = 0, cph = crankPh;
    int arms = armUp > 0.5f;
    if (tt == T_WHIP || tt == T_FOOTJAM) bikeYaw += prog * PI2;
    if (tt == T_CRANK) { bikePitch = -prog * PI2; cph += prog * PI2 * 2; }
    if (tt == T_BAR) barPh = prog * PI2 * 2;
    if (tt == T_CHICKEN) barPh = prog * PI2 * 3;

    Mat root = mMul(mT(px, py + pivH, pz), mMul(mRY(hdg + yawCur), mMul(mRX(pitch), mMul(mRZ(roll), mT(0, -pivH, 0)))));
    float lift = 0.22f * tuck;
    Mat bike = mMul(root, mMul(mT(0, 0.5f + lift, 0), mMul(mRY(bikeYaw), mMul(mRX(bikePitch), mT(0, -0.5f, 0)))));

    unsigned frame = RGB(225, 40, 40), blk = RGB(30, 30, 34);
    unsigned jersey = RGB(235, 235, 240), pants = RGB(50, 70, 140), skin = RGB(240, 195, 150), helmet = RGB(250, 190, 40);

    /* тень */
    float sg = H(px, pz) + 0.04f, dx = sinf(hdg), dz = cosf(hdg);
    float h1 = 0.9f, w1 = 0.35f;
    quad(v3(px + dx * h1 - dz * w1, sg, pz + dz * h1 + dx * w1), v3(px + dx * h1 + dz * w1, sg, pz + dz * h1 - dx * w1),
         v3(px - dx * h1 + dz * w1, sg, pz - dz * h1 - dx * w1), v3(px - dx * h1 - dz * w1, sg, pz - dz * h1 + dx * w1), RGB(55, 55, 60));

    /* байк */
    wheel(&bike, -0.52f, 0.33f, wheelRot);
    wheel(&bike, 0.52f, 0.33f, wheelRot);
    V3 rear = mPt(&bike, 0, 0.33f, -0.52f), front = mPt(&bike, 0, 0.33f, 0.52f);
    V3 crank = mPt(&bike, 0, 0.30f, 0.0f), seat = mPt(&bike, 0, 0.78f, -0.26f);
    V3 htT = mPt(&bike, 0, 0.80f, 0.40f), htB = mPt(&bike, 0, 0.55f, 0.42f), stem = mPt(&bike, 0, 0.88f, 0.40f);
    limb(rear, crank, 0.022f, frame);
    limb(crank, seat, 0.022f, frame);
    limb(seat, htT, 0.022f, frame);
    limb(crank, htB, 0.025f, frame);
    limb(htT, htB, 0.028f, frame);
    limb(htB, front, 0.022f, frame);
    limb(rear, seat, 0.02f, frame);
    limb(htT, stem, 0.02f, blk);
    float bx = 0.30f * cosf(barPh), bz = 0.30f * sinf(barPh);
    V3 gR = mPt(&bike, -bx, 0.90f, 0.40f + bz), gL = mPt(&bike, bx, 0.90f, 0.40f - bz);
    limb(gL, gR, 0.02f, blk);
    /* педали */
    float pyo = 0.17f * sinf(cph), pzo = 0.17f * cosf(cph);
    V3 pedL = mPt(&bike, 0.17f, 0.30f + pyo, pzo), pedR = mPt(&bike, -0.17f, 0.30f - pyo, -pzo);
    limb(crank, pedL, 0.015f, RGB(200, 200, 60));
    limb(crank, pedR, 0.015f, RGB(200, 200, 60));

    /* райдер */
    V3 hips = mPt(&root, 0, 0.95f, -0.22f), shoulders = mPt(&root, 0, 1.45f, -0.05f);
    limb(hips, shoulders, 0.13f, jersey);
    limb(mPt(&root, 0, 1.52f, -0.04f), mPt(&root, 0, 1.64f, -0.03f), 0.07f, skin);
    limb(mPt(&root, 0, 1.64f, -0.03f), mPt(&root, 0, 1.80f, -0.03f), 0.12f, helmet);
    /* ноги (L = поджаты: педали подняты вместе с байком) */
    limb(mPt(&root, 0.10f, 0.92f, -0.22f), pedL, 0.06f, pants);
    limb(mPt(&root, -0.10f, 0.92f, -0.22f), pedR, 0.06f, pants);
    /* руки (R = вверх) */
    V3 hL = lerp3(gL, mPt(&root, 0.30f, 1.95f, 0.10f), armUp);
    V3 hR = lerp3(gR, mPt(&root, -0.30f, 1.95f, 0.10f), armUp);
    (void)arms;
    limb(mPt(&root, 0.20f, 1.42f, -0.05f), hL, 0.045f, jersey);
    limb(mPt(&root, -0.20f, 1.42f, -0.05f), hR, 0.045f, jersey);
}

static void build_scene(void)
{
    nv = 0;
    draw_ground(px, pz);
    for (int i = 0; i < NRAMPS; i++) draw_ramp(&ramps[i]);
    draw_buildings();
    draw_rider();
}

static void draw_help(void)
{
    pspDebugScreenSetXY(3, 2);  pspDebugScreenPrintf("GROUND");
    pspDebugScreenSetXY(3, 3);  pspDebugScreenPrintf(" stick L/R ..... steer");
    pspDebugScreenSetXY(3, 4);  pspDebugScreenPrintf(" mash X ........ speed up");
    pspDebugScreenSetXY(3, 5);  pspDebugScreenPrintf(" stick down>up . bunnyhop (+X = high)");
    pspDebugScreenSetXY(3, 6);  pspDebugScreenPrintf(" D-pad L/R ..... turn 180 (fakie)");
    pspDebugScreenSetXY(3, 7);  pspDebugScreenPrintf(" fakie + /\\ .... slide; stick L/R = exit");
    pspDebugScreenSetXY(3, 9);  pspDebugScreenPrintf("AIR   (L = legs, R = arms)");
    pspDebugScreenSetXY(3, 10); pspDebugScreenPrintf(" L+X crankflip     L+O whip");
    pspDebugScreenSetXY(3, 11); pspDebugScreenPrintf(" up+L+O footjam    R+O bar");
    pspDebugScreenSetXY(3, 12); pspDebugScreenPrintf(" down+R+O chickenbar");
    pspDebugScreenSetXY(3, 13); pspDebugScreenPrintf(" D-pad L/R spins, U/D flips");
    pspDebugScreenSetXY(3, 15); pspDebugScreenPrintf("Land on wheels, finish all tricks!");
    pspDebugScreenSetXY(3, 17); pspDebugScreenPrintf("START - close");
}

int main(void)
{
    setup_callbacks();
    pspDebugScreenInit();
    pspDebugScreenSetTextColor(0xFFFFFFFF);
    pspDebugScreenEnableBackColor(0);
    sceCtrlSetSamplingCycle(0);
    sceCtrlSetSamplingMode(PSP_CTRL_MODE_ANALOG);

    /* инициализация GU */
    sceGuInit();
    sceGuStart(GU_DIRECT, list);
    sceGuDrawBuffer(GU_PSM_8888, (void *)0, BUF_W);
    sceGuDispBuffer(SCR_W, SCR_H, (void *)0x88000, BUF_W);
    sceGuDepthBuffer((void *)0x110000, BUF_W);
    sceGuOffset(2048 - (SCR_W / 2), 2048 - (SCR_H / 2));
    sceGuViewport(2048, 2048, SCR_W, SCR_H);
    sceGuDepthRange(65535, 0);
    sceGuScissor(0, 0, SCR_W, SCR_H);
    sceGuEnable(GU_SCISSOR_TEST);
    sceGuDepthFunc(GU_GEQUAL);
    sceGuEnable(GU_DEPTH_TEST);
    sceGuShadeModel(GU_FLAT);
    sceGuFog(30.0f, 85.0f, SKY);
    sceGuEnable(GU_FOG);
    sceGuFinish();
    sceGuSync(0, 0);
    sceDisplayWaitVblankStart();
    sceGuDisplay(GU_TRUE);

    SceCtrlData pad;
    unsigned oldBtn = 0;
    int help = 1;
    unsigned drawOff = 0;
    py = H(px, pz);
    camAng = hdg;

    while (1) {
        sceCtrlPeekBufferPositive(&pad, 1);
        unsigned btn = pad.Buttons, pressed = btn & ~oldBtn;
        oldBtn = btn;
        if (pressed & PSP_CTRL_START) help = !help;
        if (!help) update(btn, pressed, pad.Lx, pad.Ly);

        build_scene();
        sceKernelDcacheWritebackAll();

        sceGuStart(GU_DIRECT, list);
        sceGuClearColor(help ? RGB(10, 10, 20) : SKY);
        sceGuClearDepth(0);
        sceGuClear(GU_COLOR_BUFFER_BIT | GU_DEPTH_BUFFER_BIT);

        if (!help) {
            /* камера: сзади и сверху, плавно следует за курсом */
            camY += ((py + 2.3f) - camY) * 4.0f * DT;
            float cdx = sinf(camAng), cdz = cosf(camAng);
            ScePspFVector3 eye = {px - cdx * 6.0f, camY, pz - cdz * 6.0f};
            ScePspFVector3 ctr = {px + cdx * 2.0f, py + 1.0f, pz + cdz * 2.0f};
            ScePspFVector3 up = {0, 1, 0};
            sceGumMatrixMode(GU_PROJECTION);
            sceGumLoadIdentity();
            sceGumPerspective(62.0f, 480.0f / 272.0f, 0.3f, 300.0f);
            sceGumMatrixMode(GU_VIEW);
            sceGumLoadIdentity();
            sceGumLookAt(&eye, &ctr, &up);
            sceGumMatrixMode(GU_MODEL);
            sceGumLoadIdentity();
            sceGumUpdateMatrix();
            sceGuDrawArray(GU_TRIANGLES, GU_COLOR_8888 | GU_VERTEX_32BITF | GU_TRANSFORM_3D, nv, 0, vbuf);
        }
        sceGuFinish();
        sceGuSync(0, 0);

        /* HUD (текст рисуется в текущий draw-буфер) */
        pspDebugScreenSetOffset(drawOff);
        if (help) draw_help();
        else {
            pspDebugScreenSetXY(1, 1); pspDebugScreenPrintf("SCORE %d", score);
            if (combo > 1) { pspDebugScreenSetXY(1, 2); pspDebugScreenPrintf("COMBO x%d", combo); }
            if (pending > 0) { pspDebugScreenSetXY(1, 3); pspDebugScreenPrintf("TRICKS +%d", pending); }
            if (slide) { pspDebugScreenSetXY(1, 4); pspDebugScreenPrintf("FAKIE SLIDE"); }
            if (msgT > 0) { pspDebugScreenSetXY(24, 6); pspDebugScreenPrintf("%s", msg); }
            pspDebugScreenSetXY(1, 33); pspDebugScreenPrintf("START - help   speed %.1f", sp);
        }

        sceDisplayWaitVblankStart();
        sceGuSwapBuffers();
        drawOff ^= 0x88000;
    }
    return 0;
}
