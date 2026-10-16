/**
 * Claude Usage Stick — tela touch LVGL
 * Placa: Guition JC4832W535 (ESP32-S3, AXS15231B QSPI), 480x320 paisagem.
 *
 * Dashboard do rate-limit do Claude Code (janelas 5h e 7d, headers unified-*),
 * projecao de esgotamento da janela 5h e ritmo de uso por hora com filtro de
 * periodo. Token OAuth digitado na tela e guardado cifrado (AES-256-GCM, chave
 * derivada de um PIN de 4 digitos).
 *
 * Tokens por sessao: a API nao expoe contagem para conta de assinatura; um
 * bridge opcional (tools/token_bridge.py) soma os transcripts locais do
 * Claude Code e faz POST /tokens neste device (mDNS claude-stick.local).
 *
 * Sem botao fisico: navegacao 100% touch (swipe entre telas + slideshow).
 * Init de display/touch validado no bring-up (ver REFERENCIA-HARDWARE-LVGL.md).
 */
#include <Arduino.h>
#include <Arduino_GFX_Library.h>
#include <lvgl.h>
#include <Wire.h>
#include <WiFi.h>
#include <WebServer.h>
#include <Update.h>
#include <ESPmDNS.h>
#include <Preferences.h>
#include <LittleFS.h>
#include <time.h>
#include <math.h>
#include "config.h"
#include "touch.h"
#include "wifi_manager.h"
#include "api.h"
#include "crypto.h"
#include "accounts.h"
#include "logo_assets.h"   // Clawd + logotipo oficiais (gerado por tools/gen_logo_assets.py)
#include "partner_slot.h"   // logo de parceiro: slot gravado no .bin pelo tools/partner_logo.py

// ---- Paleta (escuro, minimalista; acento coral do Claude) ----
#define C_BG       0x000000
#define C_SURFACE  0x1A1A20   // cards sem borda
#define C_SURFACE2 0x24242C   // teclas / botoes secundarios
#define C_TRACK    0x26262E   // trilho de barras
#define C_GRID     0x232329   // linhas de grade dentro de cards
#define C_BORDER   0x30303A   // hairlines raras
#define C_TEXT     0xF2F0EC
#define C_MUTED    0x8C8C98
#define C_FAINT    0x5C5C68
#define C_ACCENT   0xD97757   // coral Claude
#define C_OK       0x4ADE80
#define C_WARN     0xFBBF24
#define C_BAD      0xF87171

// ---- Idioma (0 = portugues, 1 = english; Ajustes -> NVS "lang") ----
static uint8_t g_lang = 0;
#define TRS(pt, en) (g_lang ? (en) : (pt))

// ---- Hardware ----
Arduino_Canvas *gfx = nullptr;
static uint16_t *canvas_fb = nullptr;
AXS15231B_Touch touch_dev(TOUCH_SCL, TOUCH_SDA, TOUCH_INT, TOUCH_ADDR, TOUCH_ROTATION);
WiFiManager g_wifi;
Preferences g_prefs;

// ---- Estado da aplicação ----
enum State {
  ST_BOOT, ST_PIN, ST_SETUP_PIN, ST_WIFI, ST_TOKEN,
  ST_LOADING, ST_MAIN, ST_SETTINGS, ST_ACCOUNTS, ST_ACCT_NAME, ST_ABOUT, ST_ERROR
};
static State g_state = ST_BOOT;
static State g_pending = ST_BOOT;
static bool  g_dirty = false;
static void request_state(State s) { g_pending = s; g_dirty = true; }

// ---- Dados ----
static UsageData   g_usage = {};

// ---- Tokens por sessao (vindos do bridge via POST /tokens) ----
struct TokenStats { long long tin, tout, cache; int sessions; uint32_t atMs; };
static TokenStats g_tok = {0, 0, 0, 0, 0};
#define TOK_FRESH_MS (15UL * 60UL * 1000UL)

// ---- OpenRouter (opcional; management key cifrada com o PIN da sessao) ----
static EncryptedBlob g_orBlob;
static bool  g_hasOr = false;            // blob salvo no NVS ("orblob")
static char  g_orKey[128] = {0};         // chave decifrada (so RAM)
static OrData g_or = {};
static float g_orBase = -1.0f;           // total_usage no 1o poll do dia local
static uint32_t g_orDay = 0;             // dia (day_key) de g_orBase
static bool  g_orEntry = false;          // tela de token esta pedindo a chave OR

// ---- Token / segurança ----
static AccountSlots g_accts;
static EncryptedBlob g_blob;
static bool g_hasToken = false;              // existe conta salva no NVS
static bool g_onboarding = false;            // primeiro setup em andamento
static char g_token[200] = {0};              // token decifrado (só em RAM)
static char g_pendingToken[200] = {0};       // token digitado, aguardando PIN
// PIN da sessao: fica em RAM do desbloqueio ate o reboot, porque trocar de conta
// e adicionar conta precisam decifrar/cifrar OUTROS slots sem pedir o PIN de novo.
// Trade-off aceito: nao enfraquece o modelo — o token JA vive decifrado em
// g_token, entao quem consegue ler a RAM ja tem o que interessa. O que continua
// valendo: nada disso vai para o NVS, e factory_reset() zera este buffer.
static char g_sessionPin[PIN_LEN + 1] = {0};
// Copia do PIN da sessao em RTC RAM: sobrevive ao ESP.restart() do watchdog de
// WiFi (ver loop()) para o device voltar ao dashboard sem pedir PIN. Some ao
// desligar da energia; o setup() so aceita apos reset por software.
#define RTC_PIN_MAGIC 0xC1A0DE01u
struct RtcSession { uint32_t magic; char pin[PIN_LEN + 1]; };
RTC_NOINIT_ATTR static RtcSession g_rtc;
static void rtc_session_clear() { memset(&g_rtc, 0, sizeof(g_rtc)); }
static int  g_tokenTargetSlot = 0;
static char g_pendingLabel[ACCT_LBL_MAX] = {0};
static char g_pinEntry[PIN_LEN + 1] = {0};   // dígitos sendo digitados
static char g_pinFirst[PIN_LEN + 1] = {0};   // 1ª entrada no setup de PIN
static bool g_pinConfirming = false;         // setup: confirmando 2ª vez
static int  g_pinAttempts = 0;               // tentativas erradas (persistido)
static uint32_t g_lockoutUntil = 0;          // millis até liberar nova tentativa
static bool g_lockPainted = false;           // aviso ja esta em vermelho
static int  g_lockSecs = -1;                 // ultimo segundo renderizado
static bool g_timeInit = false;

// ---- Refresh em background ----
static bool g_wantRefresh = false;        // botão de refresh pediu atualização
static bool g_refreshing = false;         // busca em andamento
static bool g_lastFetchOk = true;         // último fetch deu certo?
static uint32_t g_lastOkMs = 0;           // millis do último sucesso (p/ "atualizado há Xs")

// ---- Brilho ----
static const uint8_t BRI_LEVELS[3] = {60, 160, 255};
static int g_briIdx = 1;
// Escurecer quando parado + modo noite (config NVS, tela e painel web)
static int  g_dimMin = 0;                 // min sem toque p/ escurecer: 0=off, 1/5/10/30
static bool g_nightOn = false;            // apaga a tela no horario abaixo
static int  g_nightFrom = 22, g_nightTo = 7;   // horas locais; pode cruzar a meia-noite
static uint8_t g_blNow = 0;               // duty atual do backlight
#define BL_DIM        18                  // brilho "escurecido"
#define NIGHT_WAKE_MS 30000UL             // de noite, um toque acende por 30s

static uint32_t g_lastPollMs = 0;         // millis do último poll (p/ barra de refresh)
static int g_pollSec = DEFAULT_POLL_SEC;  // intervalo de atualização (config, NVS)
static int g_tzOffset = -3;               // fuso GMT (horas), config NVS
static int g_weekMasc = 1;                // card SEMANA: 0=off 1=Clawd 2=rodizio 3=humor (NVS)
static bool g_weekFlip = false;           // face atual do card SEMANA (vira a cada poll)
static int g_rotIdx = 0;                  // proximo modelo do rodizio
static int g_slideSec = 0;                // slideshow: 0=off, 5/10/15/30s (config, NVS)
static uint32_t g_lastTouchMs = 0;        // ultimo toque (pausa o slideshow)
static uint32_t g_lastSlideMs = 0;

// ---- Mascotes Clawd oficiais por modelo (reservado p/ uso futuro) ----
// Sem tela propria hoje: g_mascN fica 0 e a animacao do loop() nao roda.
// mood: 0=apagado, 1=ok, 2=limitado, 3=erro, 4=dormindo
#define NMODELS 4                     // 0=Haiku 1=Sonnet 2=Opus 3=Fable
struct Mascot {
  lv_obj_t *cont, *img, *lid[2], *drop, *pupil[2], *fx[3];   // fx: particulas do humor
  lv_obj_t *heart[3], *bang;                                 // coracoes / "!" das reacoes
  int react; uint32_t reactAt;                               // reacao em curso (REACT_*)
  int baseX, baseY, mood, scale;                             // scale: 256 = 1x
  uint32_t bornMs, lookAt, lookUntil;                        // pulinho / olhar p/ os lados
};
// Reacoes a eventos (toque, janela reiniciou, passou de 90%)
enum { REACT_NONE, REACT_HOP, REACT_HEARTS, REACT_PARTY, REACT_SCARED };
static const uint16_t REACT_MS[] = {0, 600, 1600, 2000, 1500};
static int g_mascEvt = REACT_NONE;      // evento do ultimo poll, aplicado ao mostrar o mascote
#define MASC_TICK_MS 40                 // ~25 fps; se o touch pesar, voltar p/ 60-80
// prototipos explicitos: o gerador do Arduino poria os automaticos antes do struct
static void masc_scale(Mascot &m, float sx, float sy);
static void masc_tick(Mascot &m, uint32_t now, int i);
static Mascot g_masc[NMODELS];
static int g_mascN = 0;
static lv_point_precise_t g_mXPts[NMODELS][4][2];   // olhos em X (mood 3)

// ---- Ponteiros de UI do dashboard (zerados a cada build de ST_MAIN) ----
#define NTILES 2                      // 0 = Claude, 1 = OpenRouter (so com chave)
#define NSEG 18                       // segmentos do medidor de janela
struct DashUI {
  lv_obj_t *tv, *tile[NTILES], *dots[NTILES];
  lv_obj_t *refBar;
  // agora (overview + reset mesclados)
  lv_obj_t *agChip, *agPct5, *agCd5, *agAt5;
  lv_obj_t *agPct7, *agCd7, *agAt7, *agTok;
  lv_obj_t *seg5[NSEG], *seg7[NSEG];  // medidores segmentados
  lv_obj_t *wkMasc;                   // face "mascote" do card SEMANA
  // OpenRouter
  lv_obj_t *orBal, *orAt, *orFree, *orToday, *orUsed, *orChip, *orMsg;
  lv_obj_t *orSeg[NSEG];
  // header: troca Claude <-> OpenRouter conforme o tile
  lv_obj_t *hIcon, *hWord, *hOrName, *hAcct;
};
static DashUI g_ui;
static lv_obj_t *g_pinDots = nullptr, *g_pinMsg = nullptr;
static int g_curTile = 0;


// ---- Forward declarations ----
static void render_state();
static void refresh_ui_values();
static void dash_tick();
static void set_hdr_status();
static void apply_tz();
static void apply_brightness();
static void week_face_apply();
static void ui_pin();
static void pin_lock_tick();
static void ui_wifi();
static void ui_token();
static void ui_loading(const char *sub);
static void ui_main();
static void ui_settings();
static void ui_accounts();
static void ui_account_name();
static void ui_message(const char *title, const char *sub, uint32_t color);
static void nav_cb(lv_event_t *e);
static void start_data_web();
static void update_tok_row();
static void show_moment(int win, int thr);
static void or_apply(const OrData &d);
static bool or_save(const char *key, OrData &d);
static void or_remove();
static void moment_tick();
static void moment_close();

// ---- Logo personalizada no header ----
// Duas origens, mesmo formato (ARGB8888 em bytes B,G,R,A, ate PARTNER_MAX_W x
// PARTNER_MAX_H): enviada pelo painel web (LittleFS /logo.bin, carregada na
// PSRAM; vence) ou gravada no .bin pelo tools/partner_logo.py (partner_slot).
#define LOGO_FILE  "/logo.bin"
#define LOGO_MAGIC 0x4F474F4Cu               // "LOGO"
struct LogoHdr { uint32_t magic; uint16_t w, h; };
static uint8_t *g_logoPx = nullptr;          // logo do painel web (PSRAM)
static uint16_t g_logoW = 0, g_logoH = 0;
static bool     logo_present() { return g_logoPx || partnerLogoPresent(); }
static uint16_t logo_w() { return g_logoPx ? g_logoW : partnerLogoW(); }
static uint16_t logo_h() { return g_logoPx ? g_logoH : partnerLogoH(); }
// Descritor estatico reapontado a cada chamada: imagem ja criada com ele passa
// a ver a logo nova (o rebuild de tela vem logo depois).
static const lv_image_dsc_t *logo_dsc() {
  static lv_image_dsc_t d;
  d.header.magic = LV_IMAGE_HEADER_MAGIC;
  d.header.cf = LV_COLOR_FORMAT_ARGB8888;
  d.header.w = logo_w();
  d.header.h = logo_h();
  d.header.stride = d.header.w * 4;
  d.data_size = (uint32_t)d.header.w * d.header.h * 4;
  d.data = g_logoPx ? g_logoPx : g_partnerSlot.px;
  return &d;
}
// Troca a logo web (px = nullptr volta para a do .bin / wordmark).
static void logo_set(uint8_t *px, uint16_t w, uint16_t h) {
  uint8_t *old = g_logoPx;
  g_logoPx = px; g_logoW = w; g_logoH = h;
  logo_dsc();                                // reaponta antes de liberar o antigo
  if (old) heap_caps_free(old);
}
static void load_web_logo() {
  if (!LittleFS.exists(LOGO_FILE)) return;
  File f = LittleFS.open(LOGO_FILE, "r");
  LogoHdr h;
  bool ok = f && f.read((uint8_t *)&h, sizeof(h)) == sizeof(h) && h.magic == LOGO_MAGIC &&
            h.w >= 1 && h.w <= PARTNER_MAX_W && h.h >= 1 && h.h <= PARTNER_MAX_H;
  size_t n = ok ? (size_t)h.w * h.h * 4 : 0;
  uint8_t *px = ok ? (uint8_t *)heap_caps_malloc(n, MALLOC_CAP_SPIRAM) : nullptr;
  if (px && f.read(px, n) == n) logo_set(px, h.w, h.h);
  else if (px) heap_caps_free(px);
  if (f) f.close();
  Serial.printf("[LOGO] web: %s\n", g_logoPx ? "carregada" : "invalida");
}

// ============================================================
// Pipeline de display/touch (validado no bring-up)
// ============================================================
// Modo DIRECT: `px_map` e sempre o framebuffer inteiro e `area` e so o retangulo
// sujo. Transpor apenas essa area corta o grosso do custo — antes eram 153.600
// pixels em PSRAM a cada piscada de mascote ou label de 1s.
// A escrita anda contigua no destino (lx fixo => ly consecutivos sao vizinhos em
// canvas_fb), que e o lado que mais sofre com cache miss em PSRAM.
// O push QSPI (307KB) so acontece no ultimo retangulo do refresh; sem essa
// guarda o LVGL dispararia um push por area suja.
#define FLUSH_STATS 0        // 1 = loga custo de flush 1x/s no serial

static void disp_flush_cb(lv_display_t *disp, const lv_area_t *area, uint8_t *px_map) {
  const uint16_t *src = (const uint16_t *)px_map;
  const int y1 = area->y1, y2 = area->y2;
#if FLUSH_STATS
  uint32_t t0 = micros();
#endif
  for (int lx = area->x1; lx <= area->x2; lx++) {
    uint16_t *dst = canvas_fb + (479 - lx) * 320 + y1;
    const uint16_t *s = src + (size_t)y1 * SCREEN_WIDTH + lx;
    for (int ly = y1; ly <= y2; ly++) { *dst++ = *s; s += SCREEN_WIDTH; }
  }
#if FLUSH_STATS
  uint32_t t1 = micros();
#endif
  bool last = lv_display_flush_is_last(disp);
  if (last) gfx->flush();
#if FLUSH_STATS
  uint32_t t2 = micros();

  // Custo de transpor vs empurrar por QSPI. Medido: push = 40,3ms fixos (canvas
  // inteiro), transposicao = 0,11us/px. Ligar so quando for medir de novo.
  static uint32_t accT = 0, accP = 0, px = 0, frames = 0, rects = 0, at = 0;
  accT += t1 - t0; accP += t2 - t1; rects++;
  px += (uint32_t)(area->x2 - area->x1 + 1) * (area->y2 - area->y1 + 1);
  if (last) frames++;
  if (millis() - at > 1000) {
    at = millis();
    Serial.printf("[FPS] frames=%u rects=%u px/s=%u transp=%uus push=%uus\n",
                  (unsigned)frames, (unsigned)rects, (unsigned)px,
                  (unsigned)accT, (unsigned)accP);
    accT = accP = px = frames = rects = 0;
  }
#endif
  lv_disp_flush_ready(disp);
}
static void touch_read_cb(lv_indev_t *indev, lv_indev_data_t *data) {
  uint16_t x, y;
  static bool swallow = false;          // toque que acordou a tela: engole ate soltar
  if (touch_dev.touched()) {
    touch_dev.readData(&x, &y);
    data->point.x = x; data->point.y = y;
    g_lastTouchMs = millis();          // pausa o slideshow / acorda a tela
    if (g_blNow == 0) { swallow = true; apply_brightness(); }
    data->state = swallow ? LV_INDEV_STATE_RELEASED : LV_INDEV_STATE_PRESSED;
  } else {
    swallow = false;
    data->state = LV_INDEV_STATE_RELEASED;
  }
}

// ============================================================
// Helpers de UI
// ============================================================
static lv_obj_t *mklabel(lv_obj_t *p, const char *txt, const lv_font_t *font, uint32_t color) {
  lv_obj_t *l = lv_label_create(p);
  lv_label_set_text(l, txt);
  lv_obj_set_style_text_font(l, font, 0);
  lv_obj_set_style_text_color(l, lv_color_hex(color), 0);
  return l;
}
static void no_box(lv_obj_t *o) {
  lv_obj_set_style_bg_opa(o, 0, 0);
  lv_obj_set_style_border_width(o, 0, 0);
  lv_obj_set_style_pad_all(o, 0, 0);
  lv_obj_clear_flag(o, LV_OBJ_FLAG_SCROLLABLE);
}
// Botão pílula com label centralizado; user_data leva o State alvo (nav_cb).
static lv_obj_t *mkbtn(lv_obj_t *p, const char *txt, const lv_font_t *font,
                       uint32_t bg, uint32_t fg) {
  lv_obj_t *b = lv_button_create(p);
  lv_obj_set_style_bg_color(b, lv_color_hex(bg), 0);
  lv_obj_set_style_radius(b, 10, 0);
  lv_obj_set_style_shadow_width(b, 0, 0);
  lv_obj_center(mklabel(b, txt, font, fg));
  return b;
}
static uint32_t pct_color(float p) {
  if (p < 70.0f) return C_OK;
  if (p < 90.0f) return C_WARN;
  return C_BAD;
}
// gradiente contínuo verde -> âmbar -> vermelho conforme o uso cresce
static lv_color_t grad_color(float p) {
  if (p < 0) p = 0; if (p > 100) p = 100;
  if (p <= 50.0f)
    return lv_color_mix(lv_color_hex(C_WARN), lv_color_hex(C_OK), (uint8_t)(p * 255.0f / 50.0f));
  return lv_color_mix(lv_color_hex(C_BAD), lv_color_hex(C_WARN), (uint8_t)((p - 50.0f) * 255.0f / 50.0f));
}
// acende os segmentos do medidor; acesos ganham a cor do gradiente,
// apagados ficam no trilho escuro
static void set_meter(lv_obj_t **seg, float pct) {
  int filled = (int)(pct / 100.0f * NSEG + 0.5f);
  if (pct > 0.5f && filled == 0) filled = 1;
  if (filled > NSEG) filled = NSEG;
  lv_color_t col = grad_color(pct);
  for (int i = 0; i < NSEG; i++) {
    if (!seg[i]) continue;
    lv_obj_set_style_bg_color(seg[i], (i < filled) ? col : lv_color_hex(C_TRACK), 0);
    lv_obj_set_style_bg_opa(seg[i], (i < filled) ? LV_OPA_COVER : 160, 0);
  }
}
// "reseta em 1h 23m" / "2d 4h" / "agora" / "--" (relógio não sincronizado)
static void fmt_eta(uint32_t epoch, char *out, int sz) {
  time_t now = time(nullptr);
  if (now < 1000000000L || epoch == 0) { snprintf(out, sz, "--"); return; }
  long d = (long)epoch - (long)now;
  if (d <= 0) { snprintf(out, sz, "%s", TRS("agora", "now")); return; }
  int days = d / 86400; d %= 86400;
  int hrs  = d / 3600;  d %= 3600;
  int mins = d / 60;
  if (days > 0)      snprintf(out, sz, "%dd %dh", days, hrs);
  else if (hrs > 0)  snprintf(out, sz, "%dh %02dm", hrs, mins);
  else               snprintf(out, sz, "%dm", mins);
}
static void fmt_clock(uint32_t epoch, char *out, int sz) {
  if (epoch == 0 || time(nullptr) < 1000000000L) { strlcpy(out, "--:--", sz); return; }
  time_t t = (time_t)epoch; struct tm tmv;
  localtime_r(&t, &tmv);
  strftime(out, sz, "%a %H:%M", &tmv);
}
static void fmt_hm(uint32_t epoch, char *out, int sz) {
  if (epoch == 0 || time(nullptr) < 1000000000L) { strlcpy(out, "--:--", sz); return; }
  time_t t = (time_t)epoch; struct tm tmv;
  localtime_r(&t, &tmv);
  strftime(out, sz, "%H:%M", &tmv);
}
// 1234 -> "1.2k", 2345678 -> "2.3M"
static void fmt_tok(long long v, char *out, int sz) {
  if (v >= 100000000LL)     snprintf(out, sz, "%lldM", v / 1000000LL);
  else if (v >= 1000000LL)  snprintf(out, sz, "%.1fM", v / 1e6);
  else if (v >= 10000LL)    snprintf(out, sz, "%lldk", v / 1000LL);
  else if (v >= 1000LL)     snprintf(out, sz, "%.1fk", v / 1e3);
  else                      snprintf(out, sz, "%lld", v);
}

// ============================================================
// NVS / persistência
// ============================================================
static void load_persisted() {
  g_prefs.begin(NVS_NAMESPACE, false);
  accountsLoad(g_prefs, g_accts);
  if (g_accts.used[g_accts.active] &&
      accountLoadBlob(g_prefs, g_accts.active, g_blob)) {
    g_hasToken = true;
  }
  g_pinAttempts = g_prefs.getInt("pinatt", 0);
  g_briIdx = g_prefs.getInt("bri", 1);
  if (g_briIdx < 0 || g_briIdx > 2) g_briIdx = 1;
  g_dimMin = g_prefs.getInt("dim", 0);
  if (g_dimMin != 0 && g_dimMin != 1 && g_dimMin != 5 && g_dimMin != 10 && g_dimMin != 30) g_dimMin = 0;
  g_nightOn = g_prefs.getBool("night", false);
  g_nightFrom = constrain(g_prefs.getInt("nfrom", 22), 0, 23);
  g_nightTo = constrain(g_prefs.getInt("nto", 7), 0, 23);
  g_pollSec = g_prefs.getInt("poll", DEFAULT_POLL_SEC);
  if (g_pollSec < MIN_POLL_SEC || g_pollSec > MAX_POLL_SEC) g_pollSec = DEFAULT_POLL_SEC;
  g_tzOffset = g_prefs.getInt("tz", -3);
  if (g_tzOffset < -12 || g_tzOffset > 14) g_tzOffset = -3;
  g_slideSec = g_prefs.getInt("slide", 0);
  g_weekMasc = g_prefs.getInt("wmasc", 1);
  if (g_weekMasc < 0 || g_weekMasc > 3) g_weekMasc = 1;
  if (g_slideSec != 0 && g_slideSec != 5 && g_slideSec != 10 &&
      g_slideSec != 15 && g_slideSec != 30) g_slideSec = 0;
  g_lang = g_prefs.getInt("lang", 0) ? 1 : 0;
  g_hasOr = g_prefs.getBytes("orblob", &g_orBlob, sizeof(g_orBlob)) == sizeof(g_orBlob);
  g_orDay = g_prefs.getUInt("ordk", 0);
  g_orBase = g_prefs.getFloat("orbase", -1.0f);
}
static void save_attempts() { g_prefs.putInt("pinatt", g_pinAttempts); }
// Noite so vale com relogio sincronizado. from == to = janela vazia.
static bool night_now() {
  if (!g_nightOn || g_nightFrom == g_nightTo) return false;
  time_t t = time(nullptr);
  if (t < 1000000000L) return false;
  struct tm lt; localtime_r(&t, &lt);
  int h = lt.tm_hour;
  return g_nightFrom < g_nightTo ? (h >= g_nightFrom && h < g_nightTo)
                                 : (h >= g_nightFrom || h < g_nightTo);
}
static uint8_t backlight_target() {
  uint32_t idle = millis() - g_lastTouchMs;
  uint8_t full = BRI_LEVELS[g_briIdx];
  if (night_now() && idle > NIGHT_WAKE_MS) return 0;
  if (g_dimMin && idle > (uint32_t)g_dimMin * 60000UL) return full < BL_DIM ? full : BL_DIM;
  return full;
}
static void apply_brightness() { g_blNow = backlight_target(); ledcWrite(TFT_BL, g_blNow); }

static void factory_reset() {
  g_prefs.clear();              // apaga blob, pinatt, bri do namespace claude
  g_wifi.forgetAll();
  memset(&g_accts, 0, sizeof(g_accts));
  memset(g_sessionPin, 0, sizeof(g_sessionPin));
  g_pendingLabel[0] = 0;
  g_tokenTargetSlot = 0;
  memset(&g_tok, 0, sizeof(g_tok));
  g_hasToken = false;
  g_token[0] = 0; g_pendingToken[0] = 0;
  g_hasOr = false; memset(g_orKey, 0, sizeof(g_orKey)); memset(&g_or, 0, sizeof(g_or));
  g_orBase = -1.0f; g_orDay = 0;
  g_pinAttempts = 0;
  g_lockoutUntil = 0;                        // senao contamina a tela de setup
  g_onboarding = true;
  Serial.println("[RESET] tudo apagado");
}

// ============================================================
// Tela: PIN (keypad touch) — entra PIN p/ decifrar OU define novo no setup
// ============================================================
static const char *pin_map[] = {
  "1", "2", "3", "\n",
  "4", "5", "6", "\n",
  "7", "8", "9", "\n",
  LV_SYMBOL_LEFT, "0", LV_SYMBOL_OK, ""
};

static void pin_update_dots() {
  if (!g_pinDots) return;
  char dots[24] = {0};
  int len = strlen(g_pinEntry);
  for (int i = 0; i < PIN_LEN; i++) {
    strcat(dots, i < len ? "*" : "_");
    if (i < PIN_LEN - 1) strcat(dots, " ");
  }
  lv_label_set_text(g_pinDots, dots);
}

// millis() vira em ~49 dias e o deadline pode cair do outro lado da volta:
// comparar por delta assinado. O g_lockoutUntil == 0 precisa de guard proprio,
// senao o delta fica negativo sozinho a partir de 2^31 ms de uptime (~24 dias)
// e o teclado morreria sem nunca ter havido bloqueio.
// Deadline vencido e zerado na hora: parado, ele voltaria a parecer "no futuro"
// ~24,8 dias depois, quando o delta assinado da a volta.
static bool pin_locked() {
  if (g_lockoutUntil == 0) return false;
  if ((int32_t)(millis() - g_lockoutUntil) < 0) return true;
  g_lockoutUntil = 0;
  return false;
}

// O teclado destrava sozinho quando o deadline passa, mas a mensagem era
// escrita uma unica vez em pin_submit(): ficava "Aguarde 60s" na tela com o PIN
// ja aceitando digito. Este tick roda no loop() e cuida das duas pontas — conta
// regressiva enquanto trava, aviso neutro ao liberar — e e dono tambem da cor,
// para os dois estados nascerem no mesmo lugar.
static void pin_lock_tick() {
  if (!g_pinMsg) return;
  char m[64];
  if (pin_locked()) {
    if (!g_lockPainted) {
      g_lockPainted = true;
      lv_obj_set_style_text_color(g_pinMsg, lv_color_hex(C_BAD), 0);
    }
    int rem = (int)((g_lockoutUntil - millis() + 999) / 1000);
    if (rem == g_lockSecs) return;      // so reescreve quando o segundo vira
    g_lockSecs = rem;
    snprintf(m, sizeof(m), TRS("PIN errado (%d/%d). Aguarde %ds", "Wrong PIN (%d/%d). Wait %ds"),
             g_pinAttempts, MAX_PIN_ATTEMPTS, rem);
    lv_label_set_text(g_pinMsg, m);
  } else if (g_lockPainted) {
    g_lockPainted = false;
    g_lockSecs = -1;
    snprintf(m, sizeof(m), TRS("Pode tentar de novo (%d/%d)", "You can try again (%d/%d)"),
             g_pinAttempts, MAX_PIN_ATTEMPTS);
    lv_label_set_text(g_pinMsg, m);
    lv_obj_set_style_text_color(g_pinMsg, lv_color_hex(C_MUTED), 0);
  }
}

static void pin_submit() {
  if (g_state == ST_SETUP_PIN) {
    if (!g_pinConfirming) {
      strlcpy(g_pinFirst, g_pinEntry, sizeof(g_pinFirst));
      g_pinConfirming = true;
      g_pinEntry[0] = 0;
      pin_update_dots();
      if (g_pinMsg) lv_label_set_text(g_pinMsg, TRS("Confirme o PIN", "Confirm the PIN"));
      return;
    }
    // confirmando
    if (strcmp(g_pinFirst, g_pinEntry) != 0) {
      g_pinConfirming = false;
      g_pinFirst[0] = 0; g_pinEntry[0] = 0;
      pin_update_dots();
      if (g_pinMsg) lv_label_set_text(g_pinMsg, TRS("Nao bateu. Defina de novo.", "Didn't match. Set it again."));
      return;
    }
    // PIN definido -> cifra o token pendente e salva
    if (!encryptToken(g_pendingToken, g_pinEntry, g_blob)) {
      if (g_pinMsg) lv_label_set_text(g_pinMsg, TRS("Falha ao cifrar. Tente de novo.", "Encryption failed. Try again."));
      g_pinConfirming = false; g_pinFirst[0] = 0; g_pinEntry[0] = 0; pin_update_dots();
      return;
    }
    accountSave(g_prefs, g_accts, g_tokenTargetSlot, g_blob, g_pendingLabel);
    accountSetActive(g_prefs, g_accts, g_tokenTargetSlot);
    g_pendingLabel[0] = 0;
    strlcpy(g_sessionPin, g_pinEntry, sizeof(g_sessionPin));
    strlcpy(g_token, g_pendingToken, sizeof(g_token));
    memset(g_pendingToken, 0, sizeof(g_pendingToken));
    g_hasToken = true; g_onboarding = false;
    g_pinAttempts = 0; save_attempts();
    g_pinConfirming = false;
    memset(g_pinFirst, 0, sizeof(g_pinFirst));   // zera de fato: os digitos ficam
    memset(g_pinEntry, 0, sizeof(g_pinEntry));   // na RAM se so o [0] for limpo
    Serial.println("[PIN] token cifrado e salvo");
    request_state(g_wifi.isConnected() ? ST_LOADING : ST_WIFI);
    return;
  }

  // ST_PIN: tenta decifrar
  if (decryptToken(g_blob, g_pinEntry, g_token, sizeof(g_token))) {
    g_pinAttempts = 0; g_lockoutUntil = 0; save_attempts();
    strlcpy(g_sessionPin, g_pinEntry, sizeof(g_sessionPin));
    memset(g_pinEntry, 0, sizeof(g_pinEntry));
    Serial.printf("[PIN] ok, token %d chars\n", (int)strlen(g_token));
    if (!g_wifi.isConnected()) g_wifi.autoConnect(WIFI_CONNECT_TIMEOUT_MS);
    request_state(g_wifi.isConnected() ? ST_LOADING : ST_WIFI);
  } else {
    g_pinAttempts++; save_attempts();
    g_pinEntry[0] = 0; pin_update_dots();
    if (g_pinAttempts >= MAX_PIN_ATTEMPTS) {
      Serial.println("[PIN] limite estourado -> wipe");
      factory_reset();
      request_state(ST_WIFI);
      return;
    }
    int wait = LOCKOUT_BASE_SEC * (1 << (g_pinAttempts - 1));
    if (wait > 3600) wait = 3600;
    g_lockoutUntil = millis() + (uint32_t)wait * 1000;
    if (!g_lockoutUntil) g_lockoutUntil = 1;   // 0 e o sentinela de "sem bloqueio"
    g_lockSecs = -1;
    pin_lock_tick();                 // escreve ja; o loop() mantem a contagem
  }
}

static void pin_kb_cb(lv_event_t *e) {
  if (lv_event_get_code(e) != LV_EVENT_VALUE_CHANGED) return;
  if (pin_locked()) return;                  // travado
  lv_obj_t *bm = (lv_obj_t *)lv_event_get_target(e);
  uint32_t id = lv_buttonmatrix_get_selected_button(bm);
  const char *txt = lv_buttonmatrix_get_button_text(bm, id);
  if (!txt) return;
  int len = strlen(g_pinEntry);
  if (strcmp(txt, LV_SYMBOL_LEFT) == 0) {
    if (len > 0) g_pinEntry[len - 1] = 0;
    pin_update_dots();
  } else if (strcmp(txt, LV_SYMBOL_OK) == 0) {
    if (len == PIN_LEN) pin_submit();
  } else if (len < PIN_LEN) {
    g_pinEntry[len] = txt[0];
    g_pinEntry[len + 1] = 0;
    pin_update_dots();
    if (len + 1 == PIN_LEN) pin_submit();     // auto-submit ao completar
  }
}

static void ui_pin() {
  lv_obj_t *scr = lv_screen_active();
  const char *title = (g_state == ST_SETUP_PIN)
    ? (g_pinConfirming ? TRS("Confirme o PIN", "Confirm the PIN") : TRS("Defina um PIN", "Set a PIN"))
    : TRS("Digite o PIN", "Enter the PIN");
  lv_obj_t *t = mklabel(scr, title, &lv_font_montserrat_22, C_TEXT);
  lv_obj_align(t, LV_ALIGN_TOP_MID, 0, 14);

  g_pinDots = mklabel(scr, "", &lv_font_montserrat_28, C_ACCENT);
  lv_obj_align(g_pinDots, LV_ALIGN_TOP_MID, 0, 48);
  pin_update_dots();

  const char *sub = (g_state == ST_SETUP_PIN)
    ? TRS("Voce vai digita-lo a cada boot.", "You'll type it on every boot.")
    : TRS("Necessario para desbloquear o token.", "Needed to unlock the token.");
  g_pinMsg = mklabel(scr, sub, &lv_font_montserrat_14, C_MUTED);
  g_lockPainted = false;                       // label novo: estado do aviso zera
  g_lockSecs = -1;
  lv_obj_align(g_pinMsg, LV_ALIGN_TOP_MID, 0, 86);

  lv_obj_t *bm = lv_buttonmatrix_create(scr);
  lv_buttonmatrix_set_map(bm, pin_map);
  lv_obj_set_size(bm, 280, 180);
  lv_obj_align(bm, LV_ALIGN_BOTTOM_MID, 0, -10);
  lv_obj_set_style_bg_color(bm, lv_color_hex(C_BG), 0);
  lv_obj_set_style_border_width(bm, 0, 0);
  lv_obj_set_style_text_font(bm, &lv_font_montserrat_24, 0);
  lv_obj_set_style_bg_color(bm, lv_color_hex(C_SURFACE2), LV_PART_ITEMS);
  lv_obj_set_style_text_color(bm, lv_color_hex(C_TEXT), LV_PART_ITEMS);
  lv_obj_add_event_cb(bm, pin_kb_cb, LV_EVENT_VALUE_CHANGED, NULL);

  pin_lock_tick();      // se ha bloqueio pendente, ja nasce com a contagem
}

// ============================================================
// Tela: WiFi (scan + teclado)
// ============================================================
static lv_obj_t *wifi_list = nullptr, *wifi_ta = nullptr, *wifi_kb = nullptr, *wifi_status = nullptr;
static char sel_ssid[33] = {0};
static void wifi_item_cb(lv_event_t *e);

static void wifi_populate() {
  lv_obj_clean(wifi_list);
  lv_label_set_text(wifi_status, TRS("Escaneando redes...", "Scanning networks..."));
  lv_refr_now(NULL);
  WiFiManager::NetworkInfo nets[12];
  int n = g_wifi.scanNetworks(nets, 12);
  for (int i = 0; i < n; i++) {
    lv_obj_t *b = lv_list_add_button(wifi_list, LV_SYMBOL_WIFI, nets[i].ssid);
    lv_obj_set_style_bg_color(b, lv_color_hex(C_SURFACE), 0);
    lv_obj_set_style_text_color(b, lv_color_hex(C_TEXT), 0);
    lv_obj_add_event_cb(b, wifi_item_cb, LV_EVENT_CLICKED, NULL);  // clique direto no botão
  }
  lv_label_set_text(wifi_status, n > 0 ? TRS("Toque na sua rede", "Tap your network")
                                       : TRS("Nenhuma rede. Toque em Reescanear.", "No networks. Tap Rescan."));
}
static void wifi_item_cb(lv_event_t *e) {
  lv_obj_t *btn = (lv_obj_t *)lv_event_get_target(e);
  const char *txt = lv_list_get_button_text(wifi_list, btn);
  if (!txt) return;
  strlcpy(sel_ssid, txt, sizeof(sel_ssid));
  lv_label_set_text_fmt(wifi_status, TRS("Senha de \"%s\":", "Password for \"%s\":"), sel_ssid);
  lv_obj_add_flag(wifi_list, LV_OBJ_FLAG_HIDDEN);
  lv_textarea_set_text(wifi_ta, "");
  lv_obj_clear_flag(wifi_ta, LV_OBJ_FLAG_HIDDEN);
  lv_obj_clear_flag(wifi_kb, LV_OBJ_FLAG_HIDDEN);
  lv_keyboard_set_textarea(wifi_kb, wifi_ta);
}
static void wifi_kb_cb(lv_event_t *e) {
  lv_event_code_t code = lv_event_get_code(e);
  if (code == LV_EVENT_READY) {
    const char *pass = lv_textarea_get_text(wifi_ta);
    lv_label_set_text(wifi_status, TRS("Conectando...", "Connecting..."));
    lv_obj_add_flag(wifi_kb, LV_OBJ_FLAG_HIDDEN);
    lv_obj_add_flag(wifi_ta, LV_OBJ_FLAG_HIDDEN);
    lv_refr_now(NULL);
    bool ok = g_wifi.connectTo(sel_ssid, pass, 15000);
    if (ok) request_state(g_onboarding ? ST_TOKEN : ST_LOADING);
    else { lv_label_set_text(wifi_status, TRS("Falhou. Toque numa rede de novo.", "Failed. Tap a network again.")); lv_obj_clear_flag(wifi_list, LV_OBJ_FLAG_HIDDEN); }
  } else if (code == LV_EVENT_CANCEL) {
    lv_obj_add_flag(wifi_kb, LV_OBJ_FLAG_HIDDEN);
    lv_obj_add_flag(wifi_ta, LV_OBJ_FLAG_HIDDEN);
    lv_obj_clear_flag(wifi_list, LV_OBJ_FLAG_HIDDEN);
    lv_label_set_text(wifi_status, TRS("Toque na sua rede", "Tap your network"));
  }
}
static void wifi_rescan_cb(lv_event_t *e) { (void)e; wifi_populate(); }

static void ui_wifi() {
  lv_obj_t *scr = lv_screen_active();
  lv_obj_t *title = mklabel(scr, TRS("Configurar WiFi", "Configure WiFi"), &lv_font_montserrat_20, C_TEXT);
  lv_obj_align(title, LV_ALIGN_TOP_LEFT, 14, 12);

  lv_obj_t *rb = mkbtn(scr, TRS("Reescanear", "Rescan"), &lv_font_montserrat_14, C_SURFACE2, C_ACCENT);
  lv_obj_align(rb, LV_ALIGN_TOP_RIGHT, -12, 8);
  lv_obj_add_event_cb(rb, wifi_rescan_cb, LV_EVENT_CLICKED, NULL);

  if (!g_onboarding && g_hasToken) {
    lv_obj_t *bk = mkbtn(scr, TRS(LV_SYMBOL_LEFT " Voltar", LV_SYMBOL_LEFT " Back"),
                         &lv_font_montserrat_14, C_SURFACE2, C_MUTED);
    lv_obj_align(bk, LV_ALIGN_TOP_RIGHT, -150, 8);
    lv_obj_add_event_cb(bk, nav_cb, LV_EVENT_CLICKED, (void *)(intptr_t)(g_usage.ok ? ST_MAIN : ST_SETTINGS));
  }

  wifi_status = mklabel(scr, "...", &lv_font_montserrat_14, C_MUTED);
  lv_obj_align(wifi_status, LV_ALIGN_TOP_LEFT, 14, 44);

  wifi_list = lv_list_create(scr);
  lv_obj_set_size(wifi_list, 452, 246);
  lv_obj_align(wifi_list, LV_ALIGN_TOP_MID, 0, 68);
  lv_obj_set_style_bg_color(wifi_list, lv_color_hex(C_BG), 0);
  lv_obj_set_style_border_color(wifi_list, lv_color_hex(C_BORDER), 0);
  // clique é anexado por botão em wifi_populate()

  wifi_ta = lv_textarea_create(scr);
  lv_textarea_set_one_line(wifi_ta, true);
  lv_textarea_set_password_mode(wifi_ta, true);
  lv_textarea_set_placeholder_text(wifi_ta, TRS("senha do WiFi", "WiFi password"));
  lv_obj_set_size(wifi_ta, 452, 44);
  lv_obj_align(wifi_ta, LV_ALIGN_TOP_MID, 0, 66);
  lv_obj_add_flag(wifi_ta, LV_OBJ_FLAG_HIDDEN);

  wifi_kb = lv_keyboard_create(scr);
  lv_obj_add_flag(wifi_kb, LV_OBJ_FLAG_HIDDEN);
  lv_obj_add_event_cb(wifi_kb, wifi_kb_cb, LV_EVENT_ALL, NULL);

  wifi_populate();
}

// ============================================================
// WebServer: token (onboarding) + dados (bridge de tokens)
// ============================================================
static WebServer *g_web = nullptr;
static volatile bool g_tokenGot = false;
static lv_obj_t *g_tokMsg = nullptr;            // status na tela do device

static void stop_web() { if (g_web) { g_web->stop(); delete g_web; g_web = nullptr; } }

// Reboot que volta direto ao dashboard: o PIN da sessao vai para a RTC RAM e o
// setup() o consome (so apos reset por software). Usado pelo watchdog de WiFi e
// pelo fim do OTA.
static void reboot_keep_session(const char *why) {
  Serial.printf("[BOOT] reiniciando: %s\n", why);
  if (g_sessionPin[0]) {
    g_rtc.magic = RTC_PIN_MAGIC;
    strlcpy(g_rtc.pin, g_sessionPin, sizeof(g_rtc.pin));
  }
  Serial.flush();
  ESP.restart();
}

// ---- OTA pela pagina /update ----
// So aceita dentro de uma janela aberta tocando em Ajustes no proprio device:
// sem isso qualquer um na rede local gravaria um firmware que le o token.
#define OTA_WINDOW_MS (5UL * 60UL * 1000UL)
static uint32_t g_otaUntil = 0;          // 0 = fechado
static bool     g_otaBusy = false;       // Update em andamento
static bool     g_otaOk = false;         // ultimo upload terminou valido
static uint32_t g_otaBytes = 0;
static uint32_t g_otaRebootAt = 0;
static lv_obj_t *g_otaLbl = nullptr;     // progresso na lv_layer_top
static bool ota_open() {
  if (!g_otaUntil) return false;
  if ((int32_t)(millis() - g_otaUntil) < 0) return true;
  g_otaUntil = 0;
  return false;
}
static void ota_progress(const char *txt) {
  if (!g_otaLbl) {
    g_otaLbl = lv_label_create(lv_layer_top());
    lv_obj_set_style_text_font(g_otaLbl, &lv_font_montserrat_18, 0);
    lv_obj_set_style_text_color(g_otaLbl, lv_color_hex(C_TEXT), 0);
    lv_obj_set_style_bg_color(g_otaLbl, lv_color_hex(C_SURFACE2), 0);
    lv_obj_set_style_bg_opa(g_otaLbl, LV_OPA_COVER, 0);
    lv_obj_set_style_pad_all(g_otaLbl, 14, 0);
    lv_obj_set_style_radius(g_otaLbl, 12, 0);
    lv_obj_center(g_otaLbl);
  }
  lv_label_set_text(g_otaLbl, txt);
  lv_refr_now(NULL);
}
static const char OTA_CLOSED[] = "OTA fechado. No device: Ajustes > Atualizar firmware (abre por 5 min).";
static const char OTA_PAGE[] PROGMEM =
  "<!doctype html><meta charset=utf-8><meta name=viewport content='width=device-width'>"
  "<title>Claude Usage Stick - OTA</title>"
  "<body style='font-family:sans-serif;background:#000000;color:#f2f0ec;max-width:420px;margin:40px auto'>"
  "<h2>Atualizar firmware</h2>"
  "<p>Envie o <code>claude_stick.ino.bin</code>. O device reinicia sozinho e volta ao dashboard.</p>"
  "<form method=POST action=/update enctype=multipart/form-data>"
  "<input type=file name=firmware accept=.bin required> <button>Enviar</button></form>";
static void handleUpdatePage() {
  if (!ota_open()) { g_web->send(403, "text/plain; charset=utf-8", OTA_CLOSED); return; }
  g_web->send_P(200, "text/html; charset=utf-8", OTA_PAGE);
}
static void handleUpdateUpload() {
  HTTPUpload &u = g_web->upload();
  if (u.status == UPLOAD_FILE_START) {
    g_otaOk = false; g_otaBytes = 0;
    if (!ota_open()) return;             // g_otaBusy fica false: nada e gravado
    g_otaBusy = Update.begin(UPDATE_SIZE_UNKNOWN);
    Serial.printf("[OTA] inicio '%s': %s\n", u.filename.c_str(),
                  g_otaBusy ? "ok" : Update.errorString());
    ota_progress(TRS("Atualizando firmware...", "Updating firmware..."));
  } else if (u.status == UPLOAD_FILE_WRITE && g_otaBusy) {
    if (Update.write(u.buf, u.currentSize) != u.currentSize) {
      Serial.printf("[OTA] erro de escrita: %s\n", Update.errorString());
      Update.abort(); g_otaBusy = false;
      return;
    }
    g_otaBytes += u.currentSize;
    static uint32_t lastBlk = 0;
    if (g_otaBytes / 65536 != lastBlk) {  // redesenha a cada 64 KB
      lastBlk = g_otaBytes / 65536;
      char m[48];
      snprintf(m, sizeof(m), TRS("Atualizando firmware... %u KB", "Updating firmware... %u KB"),
               (unsigned)(g_otaBytes / 1024));
      ota_progress(m);
    }
  } else if (u.status == UPLOAD_FILE_END && g_otaBusy) {
    g_otaOk = Update.end(true);          // valida a imagem e troca a particao de boot
    g_otaBusy = false;
    Serial.printf("[OTA] fim: %u bytes, %s\n", (unsigned)g_otaBytes,
                  g_otaOk ? "ok" : Update.errorString());
  } else if (u.status == UPLOAD_FILE_ABORTED && g_otaBusy) {
    Update.abort(); g_otaBusy = false;
    Serial.println("[OTA] upload abortado");
  }
}
static void handleUpdateDone() {
  if (g_otaOk) {
    g_web->send(200, "text/plain; charset=utf-8", "OK. Reiniciando...");
    ota_progress(TRS("Firmware atualizado. Reiniciando...", "Firmware updated. Restarting..."));
    g_otaRebootAt = millis() + 1000;     // deixa a resposta sair antes do reboot
    return;
  }
  if (g_otaLbl) { lv_obj_delete(g_otaLbl); g_otaLbl = nullptr; }
  if (!ota_open()) { g_web->send(403, "text/plain; charset=utf-8", OTA_CLOSED); return; }
  g_web->send(500, "text/plain; charset=utf-8", String("Falha: ") + Update.errorString());
}

static bool g_mdnsUp = false;
static void ensure_mdns() {
  if (g_mdnsUp || !g_wifi.isConnected()) return;
  if (MDNS.begin("claude-stick")) {
    MDNS.addService("http", "tcp", 80);
    g_mdnsUp = true;
    Serial.println("[MDNS] claude-stick.local");
  }
}

static void anim_opa_cb(void *o, int32_t v) { lv_obj_set_style_opa((lv_obj_t *)o, (lv_opa_t)v, 0); }

// Clawd oficial (pixel-art) com "respiração" — substitui o antigo sol de raios.
static lv_obj_t *build_claude_mark(lv_obj_t *parent) {
  lv_obj_t *img = lv_image_create(parent);
  lv_image_set_src(img, &img_clawd_big);
  lv_anim_t a; lv_anim_init(&a);
  lv_anim_set_var(&a, img);
  lv_anim_set_exec_cb(&a, anim_opa_cb);
  lv_anim_set_values(&a, 140, 255);
  lv_anim_set_duration(&a, 900);
  lv_anim_set_playback_duration(&a, 900);
  lv_anim_set_repeat_count(&a, LV_ANIM_REPEAT_INFINITE);
  lv_anim_start(&a);
  return img;
}

// ---- páginas HTML ----
#define WEB_CSS \
  ":root{--bg:#000000;--card:#1A1A20;--bd:#30303A;--tx:#F2F0EC;--mut:#8C8C98;--cor:#D97757}" \
  "*{box-sizing:border-box}" \
  "body{margin:0;background:var(--bg);color:var(--tx);font-family:-apple-system,Segoe UI,Roboto,sans-serif;" \
  "display:flex;min-height:100vh;align-items:center;justify-content:center}" \
  ".card{background:var(--card);border:1px solid var(--bd);border-radius:16px;padding:26px;max-width:520px;width:92%}" \
  "h1{font-size:19px;margin:0 0 6px;display:flex;align-items:center;gap:10px}" \
  "p{color:var(--mut);font-size:14px;line-height:1.5;margin:6px 0 14px}" \
  "textarea{width:100%;background:var(--bg);color:var(--tx);border:1px solid var(--bd);border-radius:10px;" \
  "padding:12px;font-family:ui-monospace,monospace;font-size:13px;min-height:96px;resize:vertical}" \
  "input{width:100%;background:var(--bg);color:var(--tx);border:1px solid var(--bd);border-radius:10px;" \
  "padding:12px;font-size:14px;margin-bottom:10px}" \
  "button{margin-top:14px;width:100%;background:var(--cor);color:#1A1A20;border:0;border-radius:10px;" \
  "padding:14px;font-size:16px;font-weight:700;cursor:pointer}" \
  ".spark{width:26px;height:26px;flex:0 0 auto}code,a{color:var(--cor)}"

#define WEB_SPARK \
  "<svg class=spark viewBox='0 0 100 100'><g stroke='#D97757' stroke-width='12' stroke-linecap='round'>" \
  "<line x1=50 y1=9 x2=50 y2=91/><line x1=9 y1=50 x2=91 y2=50/>" \
  "<line x1=21 y1=21 x2=79 y2=79/><line x1=79 y1=21 x2=21 y2=79/>" \
  "<line x1=34 y1=11 x2=66 y2=89/><line x1=66 y1=11 x2=34 y2=89/></g></svg>"

static String web_form() {
  if (g_orEntry) return F("<!doctype html><html lang=pt><head><meta charset=utf-8>"
               "<meta name=viewport content='width=device-width,initial-scale=1'>"
               "<title>Claude Usage Stick</title><style>" WEB_CSS "</style></head><body><div class=card>"
               "<h1>OpenRouter</h1>"
               "<p>Cole uma <b>management key</b> do OpenRouter (<code>sk-or-v1-...</code>), criada em "
               "<code>openrouter.ai/settings/management-keys</code>. So ela le o saldo da conta; "
               "a chave comum de API e recusada. Fica cifrada com o seu PIN.</p>"
               "<form method=POST action='/token'>"
               "<textarea name=token placeholder='sk-or-v1-...' autocomplete=off autofocus></textarea>"
               "<button type=submit>Salvar e validar</button></form></div></body></html>");
  String h = F("<!doctype html><html lang=pt><head><meta charset=utf-8>"
               "<meta name=viewport content='width=device-width,initial-scale=1'>"
               "<title>Claude Usage Stick</title><style>" WEB_CSS "</style></head><body><div class=card>"
               "<h1>" WEB_SPARK " Claude Usage Stick</h1>"
               "<p>Cole o seu token OAuth do Claude (<code>sk-ant-oat01-...</code>) e toque em <b>Salvar</b>. "
               "O gadget vai <b>validar</b> o token e pedir um PIN na tela.</p>"
               "<form method=POST action='/token'>"
               "<input name=label maxlength=16 placeholder='rotulo da conta (ex.: Pessoal, Trabalho)' autocomplete=off>"
               "<textarea name=token placeholder='sk-ant-oat01-...' autocomplete=off autofocus></textarea>"
               "<button type=submit>Salvar e validar</button></form></div></body></html>");
  return h;
}
static String web_result(bool ok, const String &msg) {
  String h = F("<!doctype html><html lang=pt><head><meta charset=utf-8>"
               "<meta name=viewport content='width=device-width,initial-scale=1'>"
               "<title>Claude Usage Stick</title><style>" WEB_CSS "</style></head><body><div class=card>");
  if (ok && g_orEntry) {
    h += F("<h1>OpenRouter conectado</h1><p>Chave aceita. O saldo aparece no dashboard, "
           "deslizando para o lado. Pode fechar esta pagina.</p>");
  } else if (ok) {
    h += F("<h1>" WEB_SPARK " Token validado</h1>"
           "<p>Token aceito pela API. Agora <b>defina um PIN de 4 dígitos</b> na tela do gadget para finalizar. "
           "Pode fechar esta página.</p>");
  } else {
    h += F("<h1>" WEB_SPARK " Token recusado</h1><p>");
    h += msg;
    h += F("</p><p><a href='/'>Voltar e tentar de novo</a></p>");
  }
  h += F("</div></body></html>");
  return h;
}

static void handleRoot()     { g_web->send(200, "text/html; charset=utf-8", web_form()); }
static void handleNotFound() { g_web->sendHeader("Location", "/"); g_web->send(302, "text/plain", ""); }

static void handleTokenPost() {
  String lb = g_web->arg("label");
  lb.trim();
  strlcpy(g_pendingLabel, lb.c_str(), sizeof(g_pendingLabel));
  String t = g_web->arg("token");
  t.trim();
  if (t.length() < 8) {
    if (g_tokMsg) lv_label_set_text(g_tokMsg, TRS("token vazio", "empty token"));
    g_web->send(200, "text/html; charset=utf-8", web_result(false, "Token vazio ou muito curto."));
    return;
  }
  // feedback no device antes da chamada bloqueante
  if (g_tokMsg) { lv_label_set_text(g_tokMsg, TRS("validando token...", "validating token...")); lv_refr_now(NULL); }

  if (g_orEntry) {
    OrData d = {};
    bool ok = or_save(t.c_str(), d);
    if (ok) g_tokenGot = true;                  // loop -> ST_MAIN
    if (g_tokMsg) lv_label_set_text(g_tokMsg, ok ? TRS("OpenRouter conectado!", "OpenRouter connected!")
                                                 : TRS("chave recusada, tente de novo", "key rejected, try again"));
    g_web->send(200, "text/html; charset=utf-8",
                web_result(ok, String("O OpenRouter recusou a chave (") + d.error + "). Confira e cole de novo."));
    return;
  }

  UsageData tmp = {};
  bool ok = fetchUsage(t.c_str(), tmp);
  if (ok) {
    strlcpy(g_pendingToken, t.c_str(), sizeof(g_pendingToken));
    g_usage = tmp;                              // já temos dados p/ o dashboard
    g_pinConfirming = false; g_pinFirst[0] = 0; g_pinEntry[0] = 0;
    g_tokenGot = true;                          // loop -> ST_SETUP_PIN
    if (g_tokMsg) lv_label_set_text(g_tokMsg, TRS("token OK! defina o PIN", "token OK! set the PIN"));
    g_web->send(200, "text/html; charset=utf-8", web_result(true, ""));
  } else {
    String m = String("A API recusou o token (") + tmp.error + "). Confira e cole de novo.";
    if (g_tokMsg) lv_label_set_text(g_tokMsg, TRS("token recusado, tente de novo", "token rejected, try again"));
    g_web->send(200, "text/html; charset=utf-8", web_result(false, m));
  }
}

// ---- Endpoints de dados (bridge de tokens; ver tools/token_bridge.py) ----
static long long jll(const String &s, const char *key) {
  String k = String("\"") + key + "\"";
  int i = s.indexOf(k); if (i < 0) return 0;
  i = s.indexOf(':', i + k.length() - 1); if (i < 0) return 0;
  return atoll(s.c_str() + i + 1);
}
static bool jstr(const String &s, const char *key, char *out, size_t sz) {
  String k = String("\"") + key + "\"";
  int i = s.indexOf(k); if (i < 0) return false;
  i = s.indexOf(':', i + k.length()); if (i < 0) return false;
  i = s.indexOf('"', i); if (i < 0) return false;
  int e = s.indexOf('"', i + 1); if (e < 0) return false;
  strlcpy(out, s.substring(i + 1, e).c_str(), sz);
  return true;
}
static void handleWindow() {
  char b[256];
  snprintf(b, sizeof(b),
           "{\"now\":%lu,\"h5_reset\":%lu,\"d7_reset\":%lu,\"h5_util\":%.4f,\"d7_util\":%.4f,"
           "\"account\":\"%s\",\"slot\":%d}",
           (unsigned long)time(nullptr),
           (unsigned long)g_usage.h5ResetEpoch, (unsigned long)g_usage.d7ResetEpoch,
           g_usage.h5 / 100.0f, g_usage.d7 / 100.0f,
           g_accts.label[g_accts.active], g_accts.active);
  g_web->send(200, "application/json", b);
}
static void handleTokensPost() {
  String body = g_web->arg("plain");
  char acct[ACCT_LBL_MAX];
  if (jstr(body, "account", acct, sizeof(acct)) && acct[0] &&
      strcmp(acct, g_accts.label[g_accts.active]) != 0) {
    char r[96];
    snprintf(r, sizeof(r), "{\"error\":\"account_mismatch\",\"active\":\"%s\"}",
             g_accts.label[g_accts.active]);
    g_web->send(409, "application/json", r);
    return;
  }
  g_tok.tin      = jll(body, "in");
  g_tok.tout     = jll(body, "out");
  g_tok.cache    = jll(body, "cache");
  g_tok.sessions = (int)jll(body, "sessions");
  g_tok.atMs     = millis();
  Serial.printf("[TOK] in=%lld out=%lld cache=%lld sess=%d\n",
                g_tok.tin, g_tok.tout, g_tok.cache, g_tok.sessions);
  g_web->send(200, "application/json", "{\"ok\":true}");
  update_tok_row();
}
// ---- Painel web (GET /): mesmos dados da tela + ajustes pelo navegador ----
// Pagina estatica; os dados vem de /api/state (JSON) a cada 15s. Sem CDN: o
// grafico e SVG montado no JS. O token nunca sai por aqui.
static const char PANEL_PAGE[] PROGMEM = R"HTML(<!doctype html><html lang=pt><head><meta charset=utf-8>
<meta name=viewport content="width=device-width,initial-scale=1"><title>Claude Usage Stick</title>
<style>
:root{--bg:#000000;--card:#1A1A20;--bd:#30303A;--tx:#F2F0EC;--mut:#8C8C98;--cor:#D97757;--ok:#4ADE80;--warn:#FBBF24;--bad:#F87171}
*{box-sizing:border-box}body{margin:0;background:var(--bg);color:var(--tx);font-family:-apple-system,Segoe UI,Roboto,sans-serif;padding:18px}
main{max-width:760px;margin:auto}h1{font-size:20px;margin:0 0 4px}.sub{color:var(--mut);font-size:13px;margin-bottom:16px}
.row{display:grid;grid-template-columns:1fr 1fr;gap:12px}.card{background:var(--card);border:1px solid var(--bd);border-radius:16px;padding:18px;margin-bottom:12px}
.lbl{color:var(--mut);font-size:12px;letter-spacing:.08em}.pct{font-size:44px;font-weight:700;margin:4px 0}
.bar{height:8px;background:#26262E;border-radius:4px;overflow:hidden}.bar i{display:block;height:100%}
.cd{color:var(--mut);font-size:13px;margin-top:8px}
label{display:block;color:var(--mut);font-size:13px;margin:10px 0 4px}select{width:100%;background:var(--bg);color:var(--tx);border:1px solid var(--bd);border-radius:10px;padding:10px}
.grid{display:grid;grid-template-columns:1fr 1fr;gap:0 12px}button{margin-top:14px;width:100%;background:var(--cor);color:#1A1A20;border:0;border-radius:10px;padding:12px;font-weight:700;font-size:15px}
#msg{color:var(--mut);font-size:13px;margin-top:8px;min-height:1em}input[type=file]{width:100%;color:var(--mut);font-size:13px;margin-top:10px}
#otab{height:8px;background:#26262E;border-radius:4px;overflow:hidden;margin-top:12px;display:none}#otab i{display:block;height:100%;width:0;background:var(--cor)}
@media(max-width:560px){.row,.grid{grid-template-columns:1fr}}
</style></head><body><main>
<h1>Claude Usage Stick</h1><div class=sub id=sub>carregando...</div>
<div class=row>
<div class=card><div class=lbl>5 HORAS</div><div class=pct id=p5>--</div><div class=bar><i id=b5></i></div><div class=cd id=c5></div></div>
<div class=card><div class=lbl>SEMANA</div><div class=pct id=p7>--</div><div class=bar><i id=b7></i></div><div class=cd id=c7></div></div>
</div>
<div class=card id=orc style="display:none"><div class=lbl>OPENROUTER • SALDO</div><div class=pct id=orb>--</div><div class=bar><i id=orbar></i></div><div class=cd id=ord></div></div>
<form class=card id=f><div class=lbl>AJUSTES</div><div class=grid>
<div><label>Intervalo de atualizacao</label><select name=poll><option value=15>15 s<option value=30>30 s<option value=60>1 min<option value=120>2 min<option value=300>5 min</select></div>
<div><label>Brilho</label><select name=bri><option value=0>baixo<option value=1>medio<option value=2>alto</select></div>
<div><label>Fuso (GMT)</label><select name=tz id=tz></select></div>
<div><label>Slideshow</label><select name=slide><option value=0>desligado<option value=5>5 s<option value=10>10 s<option value=15>15 s<option value=30>30 s</select></div>
<div><label>Mascote semanal</label><select name=wmasc><option value=1>Clawd<option value=2>rodizio<option value=3>humor<option value=0>desligado</select></div>
<div><label>Idioma da tela</label><select name=lang><option value=0>Portugues<option value=1>English</select></div>
<div><label>Escurecer quando parado</label><select name=dim><option value=0>desligado<option value=1>apos 1 min<option value=5>apos 5 min<option value=10>apos 10 min<option value=30>apos 30 min</select></div>
<div><label>Modo noite (apaga a tela)</label><select name=night><option value=0>desligado<option value=1>ligado</select></div>
<div><label>Noite: de</label><select name=nfrom id=nfrom></select></div>
<div><label>Noite: ate</label><select name=nto id=nto></select></div>
</div><button>Salvar</button><div id=msg></div></form>
<div class=card><div class=lbl>OPENROUTER</div><div class=cd id=orst></div>
<input type=password id=ork placeholder="management key: sk-or-v1-..." autocomplete=off style="width:100%;background:var(--bg);color:var(--tx);border:1px solid var(--bd);border-radius:10px;padding:10px;margin-top:10px">
<div class=grid><button id=orsave type=button>Conectar</button><button id=ordel type=button style="background:#24242C;color:#F2F0EC">Remover</button></div>
<div id=ormsg class=cd>Crie a chave em openrouter.ai/settings/management-keys (a chave comum de API nao le o saldo).</div></div>
<div class=card><div class=lbl>LOGO DO HEADER</div><div class=cd id=lgst></div>
<canvas id=lgc width=0 height=0 style="background:#000000;border-radius:6px;margin-top:10px;max-width:100%"></canvas>
<input type=file id=lgf accept="image/png,image/svg+xml,image/jpeg,image/webp"><div class=grid>
<button id=lgup type=button>Enviar logo</button><button id=lgdel type=button style="background:#24242C;color:#F2F0EC">Remover logo</button>
</div><div id=lgmsg class=cd></div></div>
<div class=card><div class=lbl>FIRMWARE</div><div class=cd id=otast></div>
<input type=file id=fw accept=.bin><div id=otab><i id=otap></i></div>
<button id=otabtn type=button>Atualizar firmware</button><div id=otamsg class=cd></div></div>
</main><script>
const $=i=>document.getElementById(i);
for(let z=-12;z<=14;z++){const o=document.createElement('option');o.value=z;o.textContent=(z>=0?'+':'')+z;$('tz').appendChild(o)}
for(const id of['nfrom','nto'])for(let h=0;h<24;h++){const o=document.createElement('option');o.value=h;o.textContent=String(h).padStart(2,'0')+'h';$(id).appendChild(o)}
const col=p=>p>=90?'var(--bad)':p>=70?'var(--warn)':'var(--ok)';
function cd(ep,now){if(!ep||!now)return'';let s=ep-now;if(s<=0)return'resetando...';const d=Math.floor(s/86400),h=Math.floor(s%86400/3600),m=Math.floor(s%3600/60);
const t=new Date(ep*1000).toLocaleString('pt-BR',{weekday:'short',hour:'2-digit',minute:'2-digit'});return'reseta em '+(d?d+'d ':'')+h+'h'+String(m).padStart(2,'0')+' ('+t+')'}
function card(k,p,ep,now){$('p'+k).textContent=Math.round(p)+'%';$('p'+k).style.color=col(p);$('b'+k).style.width=Math.min(100,p)+'%';$('b'+k).style.background=col(p);$('c'+k).textContent=cd(ep,now)}
function orc(o){$('orc').style.display=o?'block':'none';if(!o)return;const bal=o.credits-o.used,u=o.credits>0?Math.min(100,o.used*100/o.credits):100;
$('orb').textContent='$'+bal.toFixed(2);$('orb').style.color=col(u);$('orbar').style.width=(100-u)+'%';$('orbar').style.background=col(u);
$('ord').textContent=o.ok?`hoje $${o.today.toFixed(2)} • total gasto $${o.used.toFixed(2)} de $${o.credits.toFixed(2)}`:'erro: '+o.error}
let loaded=false;
async function load(){try{const r=await fetch('/api/state');const j=await r.json();
card(5,j.h5,j.h5_reset,j.now);card(7,j.d7,j.d7_reset,j.now);orc(j.or);
$('orst').textContent=j.or?'Conectado. Saldo aparece no card acima e na 2a tela do device.':'Desconectado.';
const age=j.last_ok_s<0?'nunca':j.last_ok_s<60?j.last_ok_s+'s':Math.round(j.last_ok_s/60)+'min';
$('sub').textContent=`@${j.account} \u2022 ${j.status||'-'} \u2022 atualizado ha ${age}`+(j.fetch_ok?'':' \u2022 ultima atualizacao FALHOU')+` \u2022 v${j.fw}`;
if(!loaded){for(const k of['poll','bri','tz','slide','wmasc','lang','dim','night','nfrom','nto'])$('f')[k].value=j.cfg[k];loaded=true}
$('otast').textContent=j.ota_s>0?`Janela de OTA aberta: ${Math.floor(j.ota_s/60)}:${String(j.ota_s%60).padStart(2,'0')} restantes`
:'Janela de OTA fechada. No device: Ajustes \u2192 Atualizar firmware (abre por 5 min).';
$('lgst').textContent={web:'Logo atual: enviada pelo painel.',build:'Logo atual: gravada no firmware (--logo).',none:'Sem logo: o header mostra o texto CLAUDE CODE.'}[j.logo]||'';
$('otast').style.color=j.ota_s>0?'var(--ok)':'var(--mut)'}catch(e){$('sub').textContent='device inacessivel'}}
// Logo: recorta bordas transparentes, cabe em 170x36 e converte p/ B,G,R,A
// (mesmo pipeline do tools/partner_logo.py, so que no navegador).
let lg=null;
$('lgf').onchange=async()=>{lg=null;const f=$('lgf').files[0];if(!f)return;
try{const im=new Image();im.src=URL.createObjectURL(f);await im.decode();
let W=im.naturalWidth||512,H=im.naturalHeight||512;const k=Math.min(1,2048/Math.max(W,H));W=Math.round(W*k);H=Math.round(H*k);
const c=document.createElement('canvas');c.width=W;c.height=H;const cx=c.getContext('2d');cx.drawImage(im,0,0,W,H);
const d=cx.getImageData(0,0,W,H).data;let x0=W,y0=H,x1=-1,y1=-1;
for(let y=0;y<H;y++)for(let x=0;x<W;x++)if(d[(y*W+x)*4+3]>8){if(x<x0)x0=x;if(x>x1)x1=x;if(y<y0)y0=y;if(y>y1)y1=y}
if(x1<0){$('lgmsg').textContent='imagem vazia (tudo transparente)';return}
const bw=x1-x0+1,bh=y1-y0+1,s=Math.min(170/bw,36/bh),w=Math.max(1,Math.round(bw*s)),h=Math.max(1,Math.round(bh*s));
const o=$('lgc');o.width=w;o.height=h;const ox=o.getContext('2d');ox.imageSmoothingQuality='high';ox.clearRect(0,0,w,h);ox.drawImage(c,x0,y0,bw,bh,0,0,w,h);
const px=ox.getImageData(0,0,w,h).data,b=new Uint8Array(w*h*4);
for(let i=0;i<px.length;i+=4){b[i]=px[i+2];b[i+1]=px[i+1];b[i+2]=px[i];b[i+3]=px[i+3]}
lg={w,h,b};$('lgmsg').textContent=`${w}x${h} px \u2014 pronto para enviar (fundo transparente fica melhor)`}
catch(e){$('lgmsg').textContent='nao consegui ler a imagem'}};
$('lgup').onclick=async()=>{if(!lg){$('lgmsg').textContent='escolha uma imagem';return}
const fd=new FormData();fd.append('logo',new Blob([lg.b]),'logo.raw');$('lgmsg').textContent='enviando...';
const r=await fetch(`/api/logo?w=${lg.w}&h=${lg.h}`,{method:'POST',body:fd});$('lgmsg').textContent=r.ok?'logo aplicada':'erro: '+await r.text();load()};
$('orsave').onclick=async()=>{const k=$('ork').value.trim();if(!k){$('ormsg').textContent='cole a chave';return}
$('ormsg').textContent='validando...';const r=await fetch('/api/openrouter',{method:'POST',body:new URLSearchParams({key:k})});
$('ormsg').textContent=r.ok?'conectado':'erro: '+await r.text();if(r.ok)$('ork').value='';load()};
$('ordel').onclick=async()=>{const r=await fetch('/api/openrouter/delete',{method:'POST'});$('ormsg').textContent=r.ok?'removido':'erro';load()};
$('lgdel').onclick=async()=>{const r=await fetch('/api/logo/delete',{method:'POST'});$('lgmsg').textContent=r.ok?'logo removida':'erro';load()};
function waitBack(){$('otamsg').textContent='reiniciando... aguardando o device voltar';
const t=setInterval(async()=>{try{const r=await fetch('/api/state',{cache:'no-store'});if(r.ok){clearInterval(t);location.reload()}}catch(e){}},2000)}
$('otabtn').onclick=()=>{const f=$('fw').files[0];if(!f){$('otamsg').textContent='escolha o arquivo .bin';return}
const x=new XMLHttpRequest(),fd=new FormData();fd.append('firmware',f,f.name);
$('otab').style.display='block';$('otap').style.width='0';$('otabtn').disabled=true;
x.upload.onprogress=e=>{if(e.lengthComputable){const p=Math.round(e.loaded*100/e.total);$('otap').style.width=p+'%';$('otamsg').textContent='enviando '+p+'%'}};
x.onload=()=>{$('otabtn').disabled=false;if(x.status==200){$('otap').style.width='100%';waitBack()}else $('otamsg').textContent='erro ('+x.status+'): '+x.responseText};
x.onerror=()=>{$('otabtn').disabled=false;$('otamsg').textContent='falha de conexao durante o envio'};
x.open('POST','/update');x.send(fd)};
$('f').onsubmit=async e=>{e.preventDefault();$('msg').textContent='salvando...';
const r=await fetch('/api/settings',{method:'POST',body:new URLSearchParams(new FormData($('f')))});
$('msg').textContent=r.ok?'salvo':'erro: '+await r.text();load()};
load();setInterval(load,15000);
</script></body></html>)HTML";

// Upload da logo ja convertida pelo painel (w/h na query, pixels B,G,R,A no
// corpo multipart). Cosmetico: sem janela de toque, como os ajustes.
static uint8_t *g_logoUp = nullptr;
static size_t   g_logoUpN = 0, g_logoUpMax = 0;
static bool     g_logoUpOk = false;
static void logo_up_free() { if (g_logoUp) { heap_caps_free(g_logoUp); g_logoUp = nullptr; } }
static void logo_redraw() { if (g_state == ST_MAIN || g_state == ST_ABOUT) request_state(g_state); }
static void handleLogoUpload() {
  HTTPUpload &u = g_web->upload();
  if (u.status == UPLOAD_FILE_START) {
    logo_up_free(); g_logoUpOk = false; g_logoUpN = 0;
    int w = g_web->arg("w").toInt(), h = g_web->arg("h").toInt();
    if (w < 1 || w > PARTNER_MAX_W || h < 1 || h > PARTNER_MAX_H) return;
    g_logoUpMax = (size_t)w * h * 4;
    g_logoUp = (uint8_t *)heap_caps_malloc(g_logoUpMax, MALLOC_CAP_SPIRAM);
  } else if (u.status == UPLOAD_FILE_WRITE && g_logoUp) {
    if (g_logoUpN + u.currentSize > g_logoUpMax) { logo_up_free(); return; }
    memcpy(g_logoUp + g_logoUpN, u.buf, u.currentSize);
    g_logoUpN += u.currentSize;
  } else if (u.status == UPLOAD_FILE_END && g_logoUp) {
    g_logoUpOk = (g_logoUpN == g_logoUpMax);
  } else if (u.status == UPLOAD_FILE_ABORTED) {
    logo_up_free();
  }
}
static void handleLogoDone() {
  if (!g_logoUp || !g_logoUpOk) {
    logo_up_free();
    g_web->send(400, "text/plain; charset=utf-8", "logo invalida (tamanho ou dimensoes)");
    return;
  }
  uint16_t w = g_web->arg("w").toInt(), h = g_web->arg("h").toInt();
  LogoHdr hd = {LOGO_MAGIC, w, h};
  File f = LittleFS.open(LOGO_FILE, "w");
  bool ok = f && f.write((const uint8_t *)&hd, sizeof(hd)) == sizeof(hd) &&
            f.write(g_logoUp, g_logoUpN) == g_logoUpN;
  if (f) f.close();
  if (!ok) {
    LittleFS.remove(LOGO_FILE); logo_up_free();
    g_web->send(500, "text/plain; charset=utf-8", "falha ao gravar no LittleFS");
    return;
  }
  logo_set(g_logoUp, w, h);
  g_logoUp = nullptr; g_logoUpOk = false;
  Serial.printf("[LOGO] nova logo web %ux%u\n", w, h);
  g_web->send(200, "text/plain", "ok");
  logo_redraw();
}
static void handleLogoDelete() {
  LittleFS.remove(LOGO_FILE);
  logo_set(nullptr, 0, 0);
  Serial.println("[LOGO] logo web removida");
  g_web->send(200, "text/plain", "ok");
  logo_redraw();
}

// OpenRouter pelo painel: mesma validacao/cifra da tela de Ajustes.
static void handleOrPost() {
  String k = g_web->arg("key");
  k.trim();
  OrData d = {};
  if (k.length() < 8) { g_web->send(400, "text/plain", "chave vazia"); return; }
  if (!or_save(k.c_str(), d)) { g_web->send(400, "text/plain", d.error); return; }
  g_web->send(200, "text/plain", "ok");
  if (g_state == ST_MAIN || g_state == ST_SETTINGS) request_state(g_state);   // 2o tile / linha
}
static void handleOrDelete() {
  or_remove();
  g_web->send(200, "text/plain", "ok");
  if (g_state == ST_MAIN || g_state == ST_SETTINGS) request_state(g_state);
}

static void handlePanel() { g_web->send_P(200, "text/html; charset=utf-8", PANEL_PAGE); }

static void handleState() {
  String j;
  j.reserve(800);
  char b[512];
  long lastOk = g_lastOkMs ? (long)((millis() - g_lastOkMs) / 1000) : -1;
  snprintf(b, sizeof(b),
           "{\"now\":%lu,\"h5\":%.1f,\"d7\":%.1f,\"h5_reset\":%lu,\"d7_reset\":%lu,"
           "\"status\":\"%s\",\"fetch_ok\":%s,\"last_ok_s\":%ld,\"account\":\"%s\",\"fw\":\"" FW_VERSION "\","
           "\"ota_s\":%lu,\"logo\":\"%s\","
           "\"cfg\":{\"poll\":%d,\"bri\":%d,\"tz\":%d,\"slide\":%d,\"wmasc\":%d,\"lang\":%d,"
           "\"dim\":%d,\"night\":%d,\"nfrom\":%d,\"nto\":%d}",
           (unsigned long)time(nullptr), g_usage.h5, g_usage.d7,
           (unsigned long)g_usage.h5ResetEpoch, (unsigned long)g_usage.d7ResetEpoch,
           g_usage.statusOverall, g_lastFetchOk ? "true" : "false", lastOk,
           g_accts.label[g_accts.active],
           ota_open() ? (unsigned long)((g_otaUntil - millis()) / 1000) : 0UL,
           g_logoPx ? "web" : (partnerLogoPresent() ? "build" : "none"),
           g_pollSec, g_briIdx, g_tzOffset, g_slideSec, g_weekMasc, (int)g_lang,
           g_dimMin, g_nightOn ? 1 : 0, g_nightFrom, g_nightTo);
  j += b;
  if (g_hasOr) {
    snprintf(b, sizeof(b), ",\"or\":{\"ok\":%s,\"credits\":%.4f,\"used\":%.4f,\"today\":%.4f,\"error\":\"%s\"}",
             g_or.ok ? "true" : "false", g_or.credits, g_or.used, or_today(), g_or.error);
    j += b;
  }
  j += "}";
  g_web->send(200, "application/json", j);
}

// Aplica o que veio do formulario. Cada campo e opcional e validado contra os
// mesmos valores que os botoes da tela oferecem.
static void handleSettingsPost() {
  auto has = [](const char *k) { return g_web->hasArg(k); };
  auto num = [](const char *k) { return (int)g_web->arg(k).toInt(); };
  bool langChanged = false;
  if (has("poll")) {
    int v = num("poll");
    if (v != 15 && v != 30 && v != 60 && v != 120 && v != 300) { g_web->send(400, "text/plain", "poll"); return; }
    g_pollSec = v; g_prefs.putInt("poll", v);
  }
  if (has("bri")) {
    int v = num("bri");
    if (v < 0 || v > 2) { g_web->send(400, "text/plain", "bri"); return; }
    g_briIdx = v; g_prefs.putInt("bri", v); apply_brightness();
  }
  if (has("tz")) {
    int v = num("tz");
    if (v < -12 || v > 14) { g_web->send(400, "text/plain", "tz"); return; }
    g_tzOffset = v; g_prefs.putInt("tz", v); apply_tz();
  }
  if (has("slide")) {
    int v = num("slide");
    if (v != 0 && v != 5 && v != 10 && v != 15 && v != 30) { g_web->send(400, "text/plain", "slide"); return; }
    g_slideSec = v; g_prefs.putInt("slide", v);
  }
  if (has("wmasc")) {
    int v = num("wmasc");
    if (v < 0 || v > 3) { g_web->send(400, "text/plain", "wmasc"); return; }
    g_weekMasc = v; g_prefs.putInt("wmasc", v);
  }
  if (has("lang")) {
    int v = num("lang");
    if (v != 0 && v != 1) { g_web->send(400, "text/plain", "lang"); return; }
    langChanged = (v != g_lang);
    g_lang = (uint8_t)v; g_prefs.putInt("lang", v);
  }
  if (has("dim")) {
    int v = num("dim");
    if (v != 0 && v != 1 && v != 5 && v != 10 && v != 30) { g_web->send(400, "text/plain", "dim"); return; }
    g_dimMin = v; g_prefs.putInt("dim", v);
  }
  if (has("night")) {
    int v = num("night");
    if (v != 0 && v != 1) { g_web->send(400, "text/plain", "night"); return; }
    g_nightOn = v; g_prefs.putBool("night", g_nightOn);
  }
  if (has("nfrom")) {
    int v = num("nfrom");
    if (v < 0 || v > 23) { g_web->send(400, "text/plain", "nfrom"); return; }
    g_nightFrom = v; g_prefs.putInt("nfrom", v);
  }
  if (has("nto")) {
    int v = num("nto");
    if (v < 0 || v > 23) { g_web->send(400, "text/plain", "nto"); return; }
    g_nightTo = v; g_prefs.putInt("nto", v);
  }
  Serial.println("[WEB] ajustes atualizados pelo painel");
  g_web->send(200, "text/plain", "ok");
  // Reflete na tela: Ajustes redesenha os rotulos; idioma exige rebuild.
  if (g_state == ST_SETTINGS || (langChanged && g_state == ST_MAIN)) request_state(g_state);
  else if (g_state == ST_MAIN) week_face_apply();
}
static void start_data_web() {
  stop_web();
  ensure_mdns();
  g_web = new WebServer(80);
  g_web->on("/", HTTP_GET, handlePanel);
  g_web->on("/api/state", HTTP_GET, handleState);
  g_web->on("/api/settings", HTTP_POST, handleSettingsPost);
  g_web->on("/api/logo", HTTP_POST, handleLogoDone, handleLogoUpload);
  g_web->on("/api/logo/delete", HTTP_POST, handleLogoDelete);
  g_web->on("/api/openrouter", HTTP_POST, handleOrPost);
  g_web->on("/api/openrouter/delete", HTTP_POST, handleOrDelete);
  g_web->on("/window", HTTP_GET, handleWindow);
  g_web->on("/tokens", HTTP_POST, handleTokensPost);
  g_web->on("/update", HTTP_GET, handleUpdatePage);
  g_web->on("/update", HTTP_POST, handleUpdateDone, handleUpdateUpload);
  g_web->onNotFound([]() { g_web->send(404, "application/json", "{\"error\":\"not_found\"}"); });
  g_web->begin();
}

static void ui_token() {
  stop_web();
  lv_obj_t *scr = lv_screen_active();

  if (!g_onboarding && g_hasToken) {
    lv_obj_t *bk = mkbtn(scr, TRS(LV_SYMBOL_LEFT " Voltar", LV_SYMBOL_LEFT " Back"),
                         &lv_font_montserrat_14, C_SURFACE2, C_MUTED);
    lv_obj_align(bk, LV_ALIGN_TOP_RIGHT, -12, 8);
    lv_obj_add_event_cb(bk, nav_cb, LV_EVENT_CLICKED, (void *)(intptr_t)(g_usage.ok ? ST_MAIN : ST_SETTINGS));
  }

  if (g_orEntry) {
    lv_obj_t *mark = lv_image_create(scr);
    lv_image_set_src(mark, &img_or_mark);
    lv_obj_align(mark, LV_ALIGN_TOP_MID, 0, 40);
  } else {
    lv_obj_t *mark = build_claude_mark(scr);
    lv_obj_align(mark, LV_ALIGN_TOP_MID, 0, 8);
  }

  lv_obj_t *cap = mklabel(scr, g_orEntry ? TRS("Cole a chave do OpenRouter pelo navegador, em:",
                                               "Paste the OpenRouter key via browser, at:")
                                     : TRS("Cole o token pelo navegador, em:",
                                           "Paste the token via browser, at:"), &lv_font_montserrat_16, C_MUTED);
  lv_obj_align(cap, LV_ALIGN_TOP_MID, 0, 108);

  String url = String("http://") + WiFi.localIP().toString();
  lv_obj_t *ip = mklabel(scr, url.c_str(), &lv_font_montserrat_28, C_ACCENT);
  lv_obj_align(ip, LV_ALIGN_TOP_MID, 0, 132);

  lv_obj_t *hint = mklabel(scr, TRS("abra esse endereco no PC/celular na MESMA rede WiFi",
                                    "open this address on a PC/phone on the SAME WiFi"),
                           &lv_font_montserrat_12, C_MUTED);
  lv_obj_align(hint, LV_ALIGN_TOP_MID, 0, 174);

  lv_obj_t *sp = lv_spinner_create(scr);
  lv_spinner_set_anim_params(sp, 1200, 70);
  lv_obj_set_size(sp, 36, 36);
  lv_obj_align(sp, LV_ALIGN_BOTTOM_MID, 0, -46);
  lv_obj_set_style_arc_color(sp, lv_color_hex(C_SURFACE2), LV_PART_MAIN);
  lv_obj_set_style_arc_color(sp, lv_color_hex(C_ACCENT), LV_PART_INDICATOR);
  lv_obj_set_style_arc_width(sp, 5, LV_PART_MAIN);
  lv_obj_set_style_arc_width(sp, 5, LV_PART_INDICATOR);

  g_tokMsg = mklabel(scr, TRS("aguardando o token...", "waiting for the token..."), &lv_font_montserrat_14, C_MUTED);
  lv_obj_align(g_tokMsg, LV_ALIGN_BOTTOM_MID, 0, -14);

  // sobe o servidor web (formulario do token)
  g_web = new WebServer(80);
  g_web->on("/", HTTP_GET, handleRoot);
  g_web->on("/token", HTTP_POST, handleTokenPost);
  g_web->onNotFound(handleNotFound);
  g_web->begin();
  Serial.printf("[WEB] servidor em %s\n", url.c_str());
}

// ============================================================
// Tela: loading / mensagem
// ============================================================
static void ui_message(const char *title, const char *sub, uint32_t color) {
  lv_obj_t *scr = lv_screen_active();
  lv_obj_t *t = mklabel(scr, title, &lv_font_montserrat_24, color);
  lv_obj_align(t, LV_ALIGN_CENTER, 0, -16);
  if (sub && sub[0]) {
    lv_obj_t *s = mklabel(scr, sub, &lv_font_montserrat_16, C_MUTED);
    lv_obj_align(s, LV_ALIGN_CENTER, 0, 20);
  }
}
static void ui_loading(const char *sub) {
  lv_obj_t *scr = lv_screen_active();
  lv_obj_t *mark = build_claude_mark(scr);
  lv_obj_align(mark, LV_ALIGN_CENTER, 0, -50);
  lv_obj_t *t = mklabel(scr, TRS("Carregando seu uso...", "Loading your usage..."), &lv_font_montserrat_18, C_TEXT);
  lv_obj_align(t, LV_ALIGN_CENTER, 0, 28);
  if (sub && sub[0]) {
    lv_obj_t *s = mklabel(scr, sub, &lv_font_montserrat_12, C_MUTED);
    lv_obj_align(s, LV_ALIGN_CENTER, 0, 52);
  }
  lv_obj_t *spn = lv_spinner_create(scr);
  lv_spinner_set_anim_params(spn, 1200, 70);
  lv_obj_set_size(spn, 34, 34);
  lv_obj_align(spn, LV_ALIGN_CENTER, 0, 90);
  lv_obj_set_style_arc_color(spn, lv_color_hex(C_SURFACE2), LV_PART_MAIN);
  lv_obj_set_style_arc_color(spn, lv_color_hex(C_ACCENT), LV_PART_INDICATOR);
  lv_obj_set_style_arc_width(spn, 4, LV_PART_MAIN);
  lv_obj_set_style_arc_width(spn, 4, LV_PART_INDICATOR);
}

// ---- Boot ----
//
// O boot nao passa por request_state(): quem desenha os estados e o loop(), e ele
// so comeca depois que setup() retorna. Entre o fillScreen(preto) e esse primeiro
// render havia LittleFS (que formata na primeira vez), a migracao do historico e o
// autoConnect — bloqueante por ate 8s POR rede salva, 24s no pior caso — tudo com o
// backlight ja aceso sobre uma tela preta. Quem acabou de gravar le isso como
// travamento e desliga na tomada no meio do boot.
static lv_obj_t *g_bootSub = nullptr;

static void boot_splash(const char *sub) {
  lv_obj_t *scr = lv_screen_active();
  lv_obj_clean(scr);
  lv_obj_set_style_bg_color(scr, lv_color_hex(C_BG), 0);
  lv_obj_set_style_bg_opa(scr, LV_OPA_COVER, 0);

  lv_obj_t *mark = build_claude_mark(scr);
  lv_obj_align(mark, LV_ALIGN_CENTER, 0, -50);
  lv_obj_t *t = mklabel(scr, "Claude Usage Stick", &lv_font_montserrat_18, C_TEXT);
  lv_obj_align(t, LV_ALIGN_CENTER, 0, 28);
  g_bootSub = mklabel(scr, sub ? sub : "", &lv_font_montserrat_12, C_MUTED);
  lv_obj_align(g_bootSub, LV_ALIGN_CENTER, 0, 52);

  lv_obj_t *spn = lv_spinner_create(scr);
  lv_spinner_set_anim_params(spn, 1200, 70);
  lv_obj_set_size(spn, 34, 34);
  lv_obj_align(spn, LV_ALIGN_CENTER, 0, 90);
  lv_obj_set_style_arc_color(spn, lv_color_hex(C_SURFACE2), LV_PART_MAIN);
  lv_obj_set_style_arc_color(spn, lv_color_hex(C_ACCENT), LV_PART_INDICATOR);
  lv_obj_set_style_arc_width(spn, 4, LV_PART_MAIN);
  lv_obj_set_style_arc_width(spn, 4, LV_PART_INDICATOR);

  lv_task_handler();
  lv_refr_now(NULL);                       // o loop() ainda nao roda: forca o desenho
}

static void boot_status(const char *sub) {
  if (!g_bootSub) return;
  lv_label_set_text(g_bootSub, sub);
  lv_task_handler();
  lv_refr_now(NULL);
}

// Passado ao autoConnect: mantem o spinner girando e diz qual rede esta sendo
// tentada. So redesenha quando o texto muda — a cada 100ms um refresh completo
// de 320x480 competiria com o proprio WiFi.
static void boot_wifi_tick(const char *ssid, int idx, int total) {
  static char ultimo[64] = "";
  char s[64];
  if (total > 1) snprintf(s, sizeof(s), "%s (%d/%d)", ssid, idx, total);
  else           snprintf(s, sizeof(s), "%s", ssid);
  if (g_bootSub && strcmp(s, ultimo) != 0) {
    snprintf(ultimo, sizeof(ultimo), "%s", s);
    lv_label_set_text(g_bootSub, s);
  }
  lv_task_handler();
}

// Falha antes do LVGL existir: desenha direto no Arduino_GFX. Tambem acende o
// backlight, que fica em duty 0 desde o ledcAttach ate apply_brightness() — sem
// isso a mensagem seria escrita numa tela apagada, indistinguivel de placa morta.
static void fatal_screen(const char *msg) {
  if (gfx) {
    ledcWrite(TFT_BL, 200);
    gfx->fillScreen(0x0000);
    gfx->setTextColor(0xDBAA);             // C_ACCENT em RGB565
    gfx->setTextSize(2);
    gfx->setCursor(14, 190);
    gfx->println("FALHA AO INICIAR");
    gfx->setTextColor(0xFFFF);
    gfx->setTextSize(1);
    gfx->setCursor(14, 226);
    gfx->println(msg);
    gfx->setCursor(14, 248);
    gfx->println("Desligue e ligue a placa.");
    gfx->setCursor(14, 262);
    gfx->println("Se continuar, regrave o firmware.");
    gfx->flush();
  }
  while (1) delay(1000);
}

// dia local (dias desde epoch, corrigido pelo fuso configurado)
static uint32_t day_key() {
  time_t now = time(nullptr);
  if (now < 1000000000L) return 0;
  return (uint32_t)((now + (long)g_tzOffset * 3600) / 86400);
}

// ---- OpenRouter: saldo + gasto do dia ----
// "Hoje" = total_usage menos o total_usage do 1o poll do dia local (sem endpoint
// extra). ponytail: so o dia; 7d/30d pediriam GET /api/v1/activity (JSON grande).
static void or_apply(const OrData &d) {
  g_or = d;
  uint32_t dk = day_key();
  if (dk && (dk != g_orDay || g_orBase < 0 || d.used < g_orBase)) {
    g_orDay = dk; g_orBase = d.used;
    g_prefs.putUInt("ordk", dk); g_prefs.putFloat("orbase", d.used);
  }
}
static float or_today() {
  return (g_orBase >= 0 && g_orDay && g_orDay == day_key()) ? g_or.used - g_orBase : 0.0f;
}
static void or_poll() {
  if (!g_hasOr) return;
  if (!g_orKey[0] && !decryptToken(g_orBlob, g_sessionPin, g_orKey, sizeof(g_orKey))) {
    g_or.ok = false; strlcpy(g_or.error, "chave ilegivel", sizeof(g_or.error));
    return;
  }
  OrData d = {};
  if (fetchOpenRouter(g_orKey, d)) or_apply(d);
  else { g_or.ok = false; strlcpy(g_or.error, d.error, sizeof(g_or.error)); }
}
// Valida no OpenRouter e grava cifrada com o PIN da sessao (tela ou painel web).
static bool or_save(const char *key, OrData &d) {
  if (!g_sessionPin[0]) { strlcpy(d.error, "device bloqueado (PIN)", sizeof(d.error)); return false; }
  if (!fetchOpenRouter(key, d)) return false;
  if (!encryptToken(key, g_sessionPin, g_orBlob)) { strlcpy(d.error, "falha ao cifrar", sizeof(d.error)); return false; }
  g_prefs.putBytes("orblob", &g_orBlob, sizeof(g_orBlob));
  g_hasOr = true;
  strlcpy(g_orKey, key, sizeof(g_orKey));
  or_apply(d);
  Serial.println("[OR] chave salva");
  return true;
}
static void or_remove() {
  g_prefs.remove("orblob"); g_prefs.remove("ordk"); g_prefs.remove("orbase");
  g_hasOr = false; memset(g_orKey, 0, sizeof(g_orKey)); memset(&g_or, 0, sizeof(g_or));
  g_orBase = -1.0f; g_orDay = 0;
}
static bool switch_account(int slot) {
  if (slot < 0 || slot >= ACCT_MAX || !g_accts.used[slot] || slot == g_accts.active)
    return false;
  EncryptedBlob b;
  if (!accountLoadBlob(g_prefs, slot, b)) return false;
  char tok[200];
  if (!decryptToken(b, g_sessionPin, tok, sizeof(tok))) return false;

  accountSetActive(g_prefs, g_accts, slot);
  g_blob = b;
  strlcpy(g_token, tok, sizeof(g_token));
  memset(tok, 0, sizeof(tok));
  memset(&g_tok, 0, sizeof(g_tok));
  memset(&g_usage, 0, sizeof(g_usage));
  Serial.printf("[ACCT] conta ativa -> slot %d (%s)\n", slot, g_accts.label[slot]);
  request_state(ST_LOADING);
  return true;
}

static void finalize_pending_token() {
  EncryptedBlob nb;
  if (!encryptToken(g_pendingToken, g_sessionPin, nb)) {
    memset(g_pendingToken, 0, sizeof(g_pendingToken));
    request_state(ST_SETTINGS);
    return;
  }
  bool replacing = g_accts.used[g_tokenTargetSlot];
  bool switching = (g_tokenTargetSlot != g_accts.active);
  const char *lbl = g_pendingLabel[0] ? g_pendingLabel
                    : (replacing ? g_accts.label[g_tokenTargetSlot] : "");
  accountSave(g_prefs, g_accts, g_tokenTargetSlot, nb, lbl);
  if (switching) {
    accountSetActive(g_prefs, g_accts, g_tokenTargetSlot);
    memset(&g_tok, 0, sizeof(g_tok));
  }
  g_blob = nb;
  strlcpy(g_token, g_pendingToken, sizeof(g_token));
  memset(g_pendingToken, 0, sizeof(g_pendingToken));
  g_pendingLabel[0] = 0;
  g_hasToken = true;
  g_lastOkMs = g_lastPollMs = millis();
  g_lastFetchOk = true;
  Serial.printf("[ACCT] token salvo no slot %d (%s)\n",
                g_tokenTargetSlot, g_accts.label[g_tokenTargetSlot]);
  request_state(ST_MAIN);
}

// ============================================================
// Dashboard — helpers visuais
// ============================================================
static uint32_t status_color(const char *s) {
  if (!s || !s[0]) return C_MUTED;
  if (!strcmp(s, "rejected") || !strcmp(s, "rate_limited") || !strcmp(s, "exceeded")) return C_BAD;
  if (strstr(s, "warning")) return C_WARN;
  return C_OK;
}
static const char *overall_label(const char *s) {
  if (!s || !s[0]) return "--";
  if (!strcmp(s, "allowed")) return "OK";
  if (strstr(s, "warning"))  return TRS("ATENCAO", "WARNING");
  if (!strcmp(s, "rejected")) return TRS("BLOQUEADO", "BLOCKED");
  return s;
}

// label posicionado vazio (preenchido em refresh_ui_values/dash_tick)
static lv_obj_t *tlabel(lv_obj_t *p, const lv_font_t *f, uint32_t c, int x, int y) {
  lv_obj_t *l = lv_label_create(p);
  lv_obj_set_style_text_font(l, f, 0);
  lv_obj_set_style_text_color(l, lv_color_hex(c), 0);
  lv_label_set_text(l, "");
  lv_obj_set_pos(l, x, y);
  return l;
}
static lv_obj_t *tstatic(lv_obj_t *p, const char *txt, const lv_font_t *f, uint32_t c, int x, int y) {
  lv_obj_t *l = mklabel(p, txt, f, c);
  lv_obj_set_pos(l, x, y);
  return l;
}
static void tile_setup(lv_obj_t *t) {
  lv_obj_set_style_bg_opa(t, 0, 0);
  lv_obj_set_style_border_width(t, 0, 0);
  lv_obj_set_style_pad_all(t, 0, 0);
  lv_obj_clear_flag(t, LV_OBJ_FLAG_SCROLLABLE);
}
// card moderno: superfície arredondada SEM borda (estrutura por cor, não caixa)
static lv_obj_t *card(lv_obj_t *p, int x, int y, int w, int h) {
  lv_obj_t *c = lv_obj_create(p);
  lv_obj_set_pos(c, x, y); lv_obj_set_size(c, w, h);
  lv_obj_set_style_bg_color(c, lv_color_hex(C_SURFACE), 0);
  lv_obj_set_style_border_width(c, 0, 0);
  lv_obj_set_style_radius(c, 18, 0);
  lv_obj_set_style_pad_all(c, 14, 0);
  lv_obj_clear_flag(c, LV_OBJ_FLAG_SCROLLABLE);
  return c;
}
// chip com fundo tintado + texto na cor (mais leve que chip sólido)
static lv_obj_t *mkchip(lv_obj_t *p, int x, int y) {
  lv_obj_t *o = lv_obj_create(p);
  lv_obj_set_pos(o, x, y);
  lv_obj_set_size(o, LV_SIZE_CONTENT, 24);
  lv_obj_set_style_radius(o, 12, 0);
  lv_obj_set_style_pad_hor(o, 10, 0);
  lv_obj_set_style_pad_ver(o, 0, 0);
  lv_obj_set_style_border_width(o, 0, 0);
  lv_obj_clear_flag(o, LV_OBJ_FLAG_SCROLLABLE);
  lv_obj_t *l = lv_label_create(o);
  lv_obj_set_style_text_font(l, &lv_font_montserrat_12, 0);
  lv_label_set_text(l, ""); lv_obj_center(l);
  return o;
}
static void set_chip(lv_obj_t *o, const char *txt, uint32_t col) {
  if (!o) return;
  lv_color_t c = lv_color_hex(col);
  lv_obj_set_style_bg_color(o, lv_color_mix(c, lv_color_hex(C_BG), 60), 0);
  lv_obj_t *l = lv_obj_get_child(o, 0);
  if (l) { lv_label_set_text(l, txt[0] ? txt : "--"); lv_obj_set_style_text_color(l, c, 0); }
}
// peça retangular arredondada do mascote
static lv_obj_t *rrect(lv_obj_t *p, int x, int y, int w, int h, int r, uint32_t col) {
  lv_obj_t *o = lv_obj_create(p);
  lv_obj_set_pos(o, x, y); lv_obj_set_size(o, w, h);
  lv_obj_set_style_radius(o, r, 0);
  lv_obj_set_style_bg_color(o, lv_color_hex(col), 0);
  lv_obj_set_style_border_width(o, 0, 0);
  lv_obj_set_style_pad_all(o, 0, 0);
  lv_obj_clear_flag(o, LV_OBJ_FLAG_SCROLLABLE);
  return o;
}
// adereço pixel que identifica cada modelo (flutuando sobre a cabeça)
static void build_accessory(lv_obj_t *c, int model) {
  switch (model) {
    case 0:                              // Haiku: raio
      rrect(c, 46, 0, 8, 7, 1, C_WARN);
      rrect(c, 41, 5, 8, 7, 1, C_WARN);
      rrect(c, 46, 10, 8, 7, 1, C_WARN);
      break;
    case 1:                              // Sonnet: nota musical
      rrect(c, 50, 0, 10, 4, 1, 0x7DD3FC);
      rrect(c, 50, 0, 4, 13, 1, 0x7DD3FC);
      rrect(c, 44, 10, 8, 7, 3, 0x7DD3FC);
      break;
    case 2:                              // Opus: coroa
      rrect(c, 30, 4, 7, 8, 1, C_WARN);
      rrect(c, 41, 1, 7, 11, 1, C_WARN);
      rrect(c, 52, 4, 7, 8, 1, C_WARN);
      rrect(c, 30, 12, 29, 6, 1, C_WARN);
      break;
    case 3:                              // Fable: faisca (estrela 4 pontas)
      rrect(c, 41, 0, 6, 17, 2, 0xC4B5FD);
      rrect(c, 36, 6, 16, 6, 2, 0xC4B5FD);
      break;
  }
}

// Mascote Clawd oficial + humor + adereço. i = modelo (0..3; -1 = Clawd puro,
// sem adereço), mood = ver g_masc. Retorna o container (88x80).
static lv_obj_t *build_model_mascot(lv_obj_t *parent, int cx, int baseY, int i, int mood) {
  if (g_mascN >= NMODELS) return nullptr;
  lv_obj_t *c = lv_obj_create(parent);
  lv_obj_set_pos(c, cx - 44, baseY); lv_obj_set_size(c, 88, 80);
  lv_obj_set_style_bg_opa(c, 0, 0); lv_obj_set_style_border_width(c, 0, 0);
  lv_obj_set_style_pad_all(c, 0, 0); lv_obj_clear_flag(c, LV_OBJ_FLAG_SCROLLABLE);

  lv_obj_t *img = lv_image_create(c);
  lv_image_set_src(img, &img_clawd_md);
  lv_obj_set_pos(img, 0, 20);

  build_accessory(c, i);

  const int ex[2] = {CLAWD_MD_EYE0_X, CLAWD_MD_EYE1_X};
  const int ey = CLAWD_MD_EYE0_Y + 20, ew = CLAWD_MD_EYE0_W, eh = CLAWD_MD_EYE0_H;

  Mascot &m = g_masc[g_mascN];
  memset(&m, 0, sizeof(m));
  m.cont = c; m.img = img; m.baseX = cx - 44; m.baseY = baseY; m.mood = mood; m.scale = 256;
  m.bornMs = millis(); m.lookAt = m.bornMs + 2500;

  const int xi = i < 0 ? 0 : i;          // slot de g_mXPts
  if (mood == 1) {                       // ok: pálpebras escondidas p/ piscar
    for (int k = 0; k < 2; k++) {
      m.lid[k] = rrect(c, ex[k] - 1, ey - 1, ew + 2, eh + 2, 1, C_ACCENT);
      lv_obj_add_flag(m.lid[k], LV_OBJ_FLAG_HIDDEN);
    }
    // pupilas p/ olhar de lado: o olho do bitmap e furo transparente (mostra o
    // fundo do card), entao a pupila e da cor do fundo sobre a palpebra
    for (int k = 0; k < 2; k++) {
      m.pupil[k] = rrect(c, ex[k], ey, ew, eh, 1, C_SURFACE);
      lv_obj_add_flag(m.pupil[k], LV_OBJ_FLAG_HIDDEN);
    }
    for (int k = 0; k < 3; k++) {        // brilhos "+" subindo
      lv_obj_t *sp = rrect(c, 18 + k * 24, 16, 6, 6, 0, 0);
      lv_obj_set_style_bg_opa(sp, 0, 0);
      rrect(sp, 2, 0, 2, 6, 0, C_WARN);
      rrect(sp, 0, 2, 6, 2, 0, C_WARN);
      m.fx[k] = sp;
    }
  } else if (mood == 2) {                // limitado: gota de suor
    m.drop = rrect(c, 70, 24, 6, 10, 3, 0x7DD3FC);
    m.fx[0] = rrect(c, 12, 24, 5, 8, 3, 0x7DD3FC);   // 2a gota, do outro lado
  } else if (mood == 3) {                // erro/incidente: cinza + olhos em X
    lv_obj_set_style_image_recolor(img, lv_color_hex(0x6A6A74), 0);
    lv_obj_set_style_image_recolor_opa(img, 190, 0);
    lv_obj_set_y(img, 24);               // caidinho
    for (int k = 0; k < 2; k++) {
      g_mXPts[xi][k * 2][0]     = { (lv_value_precise_t)(ex[k] - 2), (lv_value_precise_t)(ey + 2) };
      g_mXPts[xi][k * 2][1]     = { (lv_value_precise_t)(ex[k] + ew + 2), (lv_value_precise_t)(ey + eh + 6) };
      g_mXPts[xi][k * 2 + 1][0] = { (lv_value_precise_t)(ex[k] + ew + 2), (lv_value_precise_t)(ey + 2) };
      g_mXPts[xi][k * 2 + 1][1] = { (lv_value_precise_t)(ex[k] - 2), (lv_value_precise_t)(ey + eh + 6) };
      for (int l = 0; l < 2; l++) {
        lv_obj_t *ln = lv_line_create(c);
        lv_line_set_points(ln, g_mXPts[xi][k * 2 + l], 2);
        lv_obj_set_style_line_width(ln, 3, 0);
        lv_obj_set_style_line_color(ln, lv_color_hex(C_BAD), 0);
        lv_obj_set_style_line_rounded(ln, true, 0);
      }
    }
  } else if (mood == 4) {                // n/d p/ o plano: dormindo
    lv_obj_set_style_image_recolor(img, lv_color_hex(0x6A6A74), 0);
    lv_obj_set_style_image_recolor_opa(img, 170, 0);
    for (int k = 0; k < 2; k++)
      m.lid[k] = rrect(c, ex[k] - 1, ey + eh / 2, ew + 2, eh / 2 + 1, 1, 0x8A8A94);
    lv_obj_set_style_opa(c, 180, 0);
  } else {                               // nunca sondado: apagadinho
    lv_obj_set_style_opa(c, 140, 0);
  }
  if (mood == 3) m.fx[0] = rrect(c, 37, 2, 14, 8, 4, 0x6A6A74);   // nuvenzinha
  for (int k = 0; k < 3; k++) {          // coracao pixel 7x6, oculto ate uma reacao
    lv_obj_t *h = rrect(c, 14 + k * 26, 14, 7, 6, 0, 0);
    lv_obj_set_style_bg_opa(h, 0, 0);
    rrect(h, 0, 0, 3, 3, 1, 0xF472B6); rrect(h, 4, 0, 3, 3, 1, 0xF472B6);
    rrect(h, 0, 2, 7, 2, 0, 0xF472B6); rrect(h, 1, 4, 5, 1, 0, 0xF472B6);
    rrect(h, 3, 5, 1, 1, 0, 0xF472B6);
    lv_obj_add_flag(h, LV_OBJ_FLAG_HIDDEN);
    m.heart[k] = h;
  }
  m.bang = rrect(c, 72, 0, 5, 14, 0, 0);  // "!" do susto
  lv_obj_set_style_bg_opa(m.bang, 0, 0);
  rrect(m.bang, 0, 0, 5, 9, 1, C_BAD); rrect(m.bang, 0, 11, 5, 3, 1, C_BAD);
  lv_obj_add_flag(m.bang, LV_OBJ_FLAG_HIDDEN);
  // Toque no Clawd: alterna pulinho / coracoes. Area de toque maior porque o
  // container e escalado (o hit test usa o tamanho sem escala).
  lv_obj_add_flag(c, LV_OBJ_FLAG_CLICKABLE);
  lv_obj_set_ext_click_area(c, 30);
  lv_obj_add_event_cb(c, [](lv_event_t *e) {
    lv_obj_t *t = (lv_obj_t *)lv_event_get_current_target(e);
    static int n = 0;
    for (int i = 0; i < g_mascN; i++)
      if (g_masc[i].cont == t) { g_masc[i].react = (n++ & 1) ? REACT_HEARTS : REACT_HOP; g_masc[i].reactAt = millis(); }
  }, LV_EVENT_CLICKED, NULL);
  g_mascN++;
  return c;
}

// ============================================================
// Builders dos 3 tiles
// ============================================================
// Tile 0 — AGORA: janelas 5h/semana com % grande, medidor segmentado
// (verde -> vermelho conforme o uso) e countdown grande.
static lv_obj_t *build_win_card(lv_obj_t *t, int x, const char *title,
                                lv_obj_t **pct, lv_obj_t **seg, lv_obj_t **at, lv_obj_t **cd) {
  lv_obj_t *c = card(t, x, 4, 228, 194);
  tstatic(c, title, &lv_font_montserrat_14, C_MUTED, 0, 0);
  *pct = tlabel(c, &lv_font_montserrat_48, C_OK, 0, 20);
  for (int i = 0; i < NSEG; i++)                    // medidor: 18 segmentos
    seg[i] = rrect(c, i * 11, 82, 8, 16, 2, C_TRACK);
  *at = tlabel(c, &lv_font_montserrat_12, C_FAINT, 0, 106);
  *cd = tlabel(c, &lv_font_montserrat_40, C_TEXT, 0, 124);
  return c;
}

// Face alternativa do card SEMANA: mascote Clawd animado. Alterna com o consumo
// semanal a cada poll (g_weekFlip, virado no bg_refresh). Painel opaco por cima
// do conteudo do card; reconstruido a cada aparicao (rodizio/humor mudam).
static void week_face_apply() {
  lv_obj_t *p = g_ui.wkMasc;
  if (!p) return;
  if (!g_weekMasc || !g_weekFlip) { lv_obj_add_flag(p, LV_OBJ_FLAG_HIDDEN); return; }
  lv_obj_clean(p);
  g_mascN = 0;                           // unico dono de g_masc hoje
  static const char *NAMES[NMODELS] = {"HAIKU", "SONNET", "OPUS", "FABLE"};
  int model = -1, mood = 1;
  char title[32] = "CLAWD";
  if (g_weekMasc == 2) {                 // rodizio dos 4 modelos
    model = g_rotIdx++ % NMODELS;
    strlcpy(title, NAMES[model], sizeof(title));
  } else if (g_weekMasc == 3) {          // humor pelo uso semanal
    float d = g_usage.d7;
    mood = d < 70 ? 1 : (d < 90 ? 2 : 3);
    snprintf(title, sizeof(title), "CLAWD \xE2\x80\xA2 %d%%", (int)(d + 0.5f));
  }
  tstatic(p, title, &lv_font_montserrat_14, C_MUTED, 0, 0);
  // area util 200x166 (card 228x194, pad 14); centro do mascote em (100, 94)
  lv_obj_t *m = build_model_mascot(p, 100, 94 - 40, model, mood);
  if (m) {
    // ponytail: escala via transform = render em layer; se pesar, voltar p/ 1x
    lv_obj_set_style_transform_pivot_x(m, 44, 0);
    lv_obj_set_style_transform_pivot_y(m, 40, 0);
    lv_obj_set_style_transform_scale(m, 460, 0);   // 256 = 1x
    g_masc[g_mascN - 1].scale = 460;               // base da respiracao/achatamento
    if (g_mascEvt) {                               // reacao depois do pulinho de entrada
      g_masc[g_mascN - 1].react = g_mascEvt;
      g_masc[g_mascN - 1].reactAt = millis() + 700;
      g_mascEvt = REACT_NONE;
    }
  }
  lv_obj_clear_flag(p, LV_OBJ_FLAG_HIDDEN);
}
static void build_tile_agora(lv_obj_t *t) {
  build_win_card(t, 8,   TRS("5 HORAS", "5 HOURS"), &g_ui.agPct5, g_ui.seg5, &g_ui.agAt5, &g_ui.agCd5);
  lv_obj_t *wk = build_win_card(t, 244, TRS("SEMANA", "WEEK"), &g_ui.agPct7, g_ui.seg7, &g_ui.agAt7, &g_ui.agCd7);
  lv_obj_t *p = lv_obj_create(wk);
  lv_obj_set_pos(p, 0, 0); lv_obj_set_size(p, 200, 166);
  lv_obj_set_style_bg_color(p, lv_color_hex(C_SURFACE), 0);
  lv_obj_set_style_bg_opa(p, LV_OPA_COVER, 0);
  lv_obj_set_style_border_width(p, 0, 0); lv_obj_set_style_radius(p, 0, 0);
  lv_obj_set_style_pad_all(p, 0, 0); lv_obj_clear_flag(p, LV_OBJ_FLAG_SCROLLABLE);
  g_ui.wkMasc = p;
  week_face_apply();
  g_ui.agChip = mkchip(t, 8, 204);
  g_ui.agTok = tlabel(t, &lv_font_montserrat_12, C_MUTED, 130, 210);
  lv_obj_set_width(g_ui.agTok, 342);
  lv_obj_set_style_text_align(g_ui.agTok, LV_TEXT_ALIGN_RIGHT, 0);
}
// Tile 1 — OPENROUTER: saldo da conta + gasto do dia (so com chave configurada).
static void build_tile_or(lv_obj_t *t) {
  build_win_card(t, 8, TRS("SALDO", "BALANCE"), &g_ui.orBal, g_ui.orSeg, &g_ui.orAt, &g_ui.orFree);
  lv_obj_t *c = card(t, 244, 4, 228, 194);
  tstatic(c, TRS("GASTO HOJE", "SPENT TODAY"), &lv_font_montserrat_14, C_MUTED, 0, 0);
  g_ui.orToday = tlabel(c, &lv_font_montserrat_48, C_TEXT, 0, 20);
  tstatic(c, TRS("TOTAL GASTO", "TOTAL SPENT"), &lv_font_montserrat_14, C_MUTED, 0, 106);
  g_ui.orUsed = tlabel(c, &lv_font_montserrat_28, C_TEXT, 0, 128);
  g_ui.orChip = mkchip(t, 8, 204);
  g_ui.orMsg = tlabel(t, &lv_font_montserrat_12, C_MUTED, 130, 210);
  lv_obj_set_width(g_ui.orMsg, 342);
  lv_obj_set_style_text_align(g_ui.orMsg, LV_TEXT_ALIGN_RIGHT, 0);
}
static void or_refresh_ui() {
  if (!g_ui.orBal) return;
  char b[64];
  bool have = g_or.credits > 0 || g_or.used > 0;
  float bal = g_or.credits - g_or.used;
  float usedPct = g_or.credits > 0 ? g_or.used * 100.0f / g_or.credits : 100.0f;
  if (usedPct > 100) usedPct = 100;
  if (have) snprintf(b, sizeof(b), "$%.2f", bal); else strlcpy(b, "--", sizeof(b));
  lv_label_set_text(g_ui.orBal, b);
  lv_obj_set_style_text_color(g_ui.orBal, grad_color(have ? usedPct : 0), 0);
  set_meter(g_ui.orSeg, have ? usedPct : 0);
  snprintf(b, sizeof(b), TRS("LIVRE DE $%.2f COMPRADOS", "LEFT OF $%.2f PURCHASED"), g_or.credits);
  lv_label_set_text(g_ui.orAt, have ? b : "");
  if (have) snprintf(b, sizeof(b), "%d%%", (int)(100.0f - usedPct + 0.5f)); else strlcpy(b, "", sizeof(b));
  lv_label_set_text(g_ui.orFree, b);
  if (have) snprintf(b, sizeof(b), "$%.2f", or_today()); else strlcpy(b, "--", sizeof(b));
  lv_label_set_text(g_ui.orToday, b);
  if (have) snprintf(b, sizeof(b), "$%.2f", g_or.used); else strlcpy(b, "--", sizeof(b));
  lv_label_set_text(g_ui.orUsed, b);

  if (!g_or.ok && g_or.error[0]) set_chip(g_ui.orChip, TRS("ERRO", "ERROR"), C_BAD);
  else if (!have)                set_chip(g_ui.orChip, "--", C_MUTED);
  else if (bal <= 0)             set_chip(g_ui.orChip, TRS("SEM SALDO", "NO CREDITS"), C_BAD);
  else if (usedPct >= 90)        set_chip(g_ui.orChip, TRS("SALDO BAIXO", "LOW BALANCE"), C_WARN);
  else                           set_chip(g_ui.orChip, "OK", C_OK);
  lv_label_set_text(g_ui.orMsg, g_or.ok ? TRS("gasto hoje conta a partir do 1o poll do dia",
                                              "today counts from the day's first poll")
                                        : g_or.error);
}

static void on_tile_changed(lv_event_t *e) {
  (void)e;
  if (!g_ui.tv) return;
  lv_obj_t *act = lv_tileview_get_tile_active(g_ui.tv);
  for (int i = 0; i < NTILES; i++) {
    if (!g_ui.dots[i]) continue;
    bool on = (g_ui.tile[i] == act);
    if (on) g_curTile = i;
    lv_obj_set_style_bg_color(g_ui.dots[i], lv_color_hex(on ? C_ACCENT : C_BORDER), 0);
    lv_obj_set_width(g_ui.dots[i], on ? 18 : 8);
  }
  // header segue o provedor do tile visivel
  bool orTile = g_ui.tile[1] && act == g_ui.tile[1];
  g_curTile = orTile ? 1 : 0;
  if (g_ui.hIcon) {
    lv_image_set_src(g_ui.hIcon, orTile ? &img_or_mark : &img_clawd_sm);
    lv_obj_set_pos(g_ui.hIcon, 12, orTile ? 13 : 10);
  }
  if (g_ui.hOrName) {
    if (orTile) { lv_obj_add_flag(g_ui.hWord, LV_OBJ_FLAG_HIDDEN); lv_obj_clear_flag(g_ui.hOrName, LV_OBJ_FLAG_HIDDEN); }
    else        { lv_obj_clear_flag(g_ui.hWord, LV_OBJ_FLAG_HIDDEN); lv_obj_add_flag(g_ui.hOrName, LV_OBJ_FLAG_HIDDEN); }
  }
  if (g_ui.hAcct) {                           // @conta e do Claude
    if (orTile) lv_obj_add_flag(g_ui.hAcct, LV_OBJ_FLAG_HIDDEN);
    else        lv_obj_clear_flag(g_ui.hAcct, LV_OBJ_FLAG_HIDDEN);
  }
}

// ============================================================
// Atualização de valores
// ============================================================
static void update_tok_row() {
  if (!g_ui.agTok) return;
  if (g_tok.atMs == 0 || millis() - g_tok.atMs > TOK_FRESH_MS) {
    lv_label_set_text(g_ui.agTok, "");
    return;
  }
  char a[16], b[16], s[96];
  fmt_tok(g_tok.tin, a, sizeof(a));
  fmt_tok(g_tok.tout, b, sizeof(b));
  snprintf(s, sizeof(s), TRS("tokens na janela: %s entrada \xE2\x80\xA2 %s saida",
                             "window tokens: %s in \xE2\x80\xA2 %s out"), a, b);
  lv_label_set_text(g_ui.agTok, s);
}

// Contadores/relógios (1s) — separado dos valores de fetch.
static void dash_tick() {
  if (g_state != ST_MAIN || !g_ui.agCd5) return;
  char e[32], c[24], b[64];
  fmt_eta(g_usage.h5ResetEpoch, e, sizeof(e));
  lv_label_set_text(g_ui.agCd5, e);
  fmt_clock(g_usage.h5ResetEpoch, c, sizeof(c));
  snprintf(b, sizeof(b), TRS("RESETA EM \xE2\x80\xA2 %s", "RESETS \xE2\x80\xA2 %s"), c);
  lv_label_set_text(g_ui.agAt5, b);

  fmt_eta(g_usage.d7ResetEpoch, e, sizeof(e));
  lv_label_set_text(g_ui.agCd7, e);
  fmt_clock(g_usage.d7ResetEpoch, c, sizeof(c));
  snprintf(b, sizeof(b), TRS("RESETA EM \xE2\x80\xA2 %s", "RESETS \xE2\x80\xA2 %s"), c);
  lv_label_set_text(g_ui.agAt7, b);

  set_hdr_status();
}

// ============================================================
// Momentos — animações de limiar (25/50/70/100% nas janelas 5h e semanal)
// Overlay em lv_layer_top: Clawd XL com "humor" por nível + contador de %
// + medidor acendendo. Dispara ao cruzar o limiar; toque dispensa.
// Animação 100% procedural (moment_tick no loop), sem lv_anim pendurado.
// ============================================================
static const uint8_t THR[4] = {25, 50, 70, 100};
struct MomentUI {
  lv_obj_t *scrim, *box, *img, *pct, *seg[NSEG];
  lv_obj_t *lid[2], *drop[2], *ring, *xline[4];
  int win, thr, fromPct, toPct;         // thr 0 = "janela renovada"
  int boxY;
  uint32_t t0;
};
static MomentUI g_mo = {};
static uint32_t g_momentUntil = 0;
static int g_pendWin = -1, g_pendThr = 0;      // momento aguardando exibição
static uint8_t g_thrFired[2] = {0, 0};         // bits já disparados por janela
static float g_thrPrev[2] = {-1, -1};
static bool g_thrBase = false;
static float g_renewFrom = 0;                  // % da janela 5h antes do reset
static lv_point_precise_t g_moXPts[4][2];      // olhos em X (KO)

// Detecta cruzamento de limiar após cada fetch. Baseline no 1º fetch (não
// dispara pelo que já estava acima); zera quando a janela reseta (queda >15pp).
static void check_thresholds() {
  float c[2] = {g_usage.h5, g_usage.d7};
  for (int w = 0; w < 2; w++) {
    if (g_thrBase && (g_thrPrev[w] - c[w]) > 15.0f && g_mascEvt != REACT_SCARED)
      g_mascEvt = REACT_PARTY;           // janela reiniciou: Clawd comemora
    if (w == 0 && g_thrBase && (g_thrPrev[w] - c[w]) > 15.0f) {
      g_renewFrom = g_thrPrev[w];          // aviso "janela renovada", contador desce ate o atual
      g_pendWin = 0; g_pendThr = 0;
    }
    if (!g_thrBase || (g_thrPrev[w] - c[w]) > 15.0f) {
      g_thrFired[w] = 0;
      for (int i = 0; i < 4; i++) if (c[w] >= THR[i]) g_thrFired[w] |= 1 << i;
    } else {
      int hit = -1;
      for (int i = 0; i < 4; i++)
        if (c[w] >= THR[i] && !(g_thrFired[w] & (1 << i))) { g_thrFired[w] |= 1 << i; hit = i; }
      if (hit >= 0) { g_pendWin = w; g_pendThr = THR[hit]; }
    }
    if (g_thrBase && g_thrPrev[w] < 90.0f && c[w] >= 90.0f)
      g_mascEvt = REACT_SCARED;          // cruzou 90%: Clawd se assusta
    g_thrPrev[w] = c[w];
  }
  g_thrBase = true;
}

static void moment_close() {
  if (!g_mo.scrim) return;
  lv_obj_delete(g_mo.scrim);
  memset(&g_mo, 0, sizeof(g_mo));
}
static void moment_close_cb(lv_event_t *e) { (void)e; moment_close(); }

static void show_moment(int win, int thr) {
  moment_close();
  g_mo.win = win; g_mo.thr = thr;
  if (thr == 0) {                       // janela renovada: desce do % antigo ao atual
    g_mo.fromPct = (int)(g_renewFrom + 0.5f);
    g_mo.toPct = (int)(g_usage.h5 + 0.5f);
  } else {
    g_mo.fromPct = (thr == 25) ? 0 : (thr == 50) ? 25 : (thr == 70) ? 50 : 70;
    g_mo.toPct = thr;
  }
  g_mo.t0 = millis();
  g_momentUntil = g_mo.t0 + 4600;

  lv_obj_t *s = lv_obj_create(lv_layer_top());
  g_mo.scrim = s;
  lv_obj_set_pos(s, 0, 0); lv_obj_set_size(s, 480, 320);
  lv_obj_set_style_bg_color(s, lv_color_hex(0x0D0D10), 0);
  lv_obj_set_style_bg_opa(s, 248, 0);
  lv_obj_set_style_border_width(s, 0, 0);
  lv_obj_set_style_radius(s, 0, 0);
  lv_obj_set_style_pad_all(s, 0, 0);
  lv_obj_clear_flag(s, LV_OBJ_FLAG_SCROLLABLE);
  lv_obj_add_flag(s, LV_OBJ_FLAG_CLICKABLE);
  lv_obj_add_event_cb(s, moment_close_cb, LV_EVENT_CLICKED, NULL);

  // anel de alerta (só no 100%; pisca no tick)
  if (thr == 100) {
    g_mo.ring = lv_obj_create(s);
    lv_obj_set_pos(g_mo.ring, 4, 4); lv_obj_set_size(g_mo.ring, 472, 312);
    lv_obj_set_style_bg_opa(g_mo.ring, 0, 0);
    lv_obj_set_style_radius(g_mo.ring, 14, 0);
    lv_obj_set_style_border_width(g_mo.ring, 4, 0);
    lv_obj_set_style_border_color(g_mo.ring, lv_color_hex(C_BAD), 0);
    lv_obj_clear_flag(g_mo.ring, LV_OBJ_FLAG_SCROLLABLE);
    lv_obj_clear_flag(g_mo.ring, LV_OBJ_FLAG_CLICKABLE);
  }

  // caixa do Clawd (a caixa inteira anima: bounce / shake / queda de entrada)
  g_mo.boxY = 110;
  lv_obj_t *bx = lv_obj_create(s);
  g_mo.box = bx;
  lv_obj_set_pos(bx, 36, g_mo.boxY - 40);
  lv_obj_set_size(bx, 176, 116);
  lv_obj_set_style_bg_opa(bx, 0, 0);
  lv_obj_set_style_border_width(bx, 0, 0);
  lv_obj_set_style_pad_all(bx, 0, 0);
  lv_obj_clear_flag(bx, LV_OBJ_FLAG_SCROLLABLE);
  lv_obj_clear_flag(bx, LV_OBJ_FLAG_CLICKABLE);

  g_mo.img = lv_image_create(bx);
  lv_image_set_src(g_mo.img, &img_clawd_xl);
  lv_obj_set_pos(g_mo.img, 0, 0);

  // humores (sobre os buracos dos olhos do sprite)
  const int ex[2] = {CLAWD_XL_EYE0_X, CLAWD_XL_EYE1_X};
  const int ey = CLAWD_XL_EYE0_Y, ew = CLAWD_XL_EYE0_W, eh = CLAWD_XL_EYE0_H;
  if (thr == 50) {
    // focado: pálpebras cobrindo metade dos olhos + 1 gota de suor
    for (int i = 0; i < 2; i++)
      g_mo.lid[i] = rrect(bx, ex[i] - 1, ey - 1, ew + 2, eh / 2 + 2, 0, C_ACCENT);
    g_mo.drop[0] = rrect(bx, 150, 6, 8, 12, 4, 0x7DD3FC);
  } else if (thr == 70) {
    // preocupado: olhos arregalados + 2 gotas (a caixa treme no tick)
    for (int i = 0; i < 2; i++)
      g_mo.lid[i] = rrect(bx, ex[i] - 3, ey - 4, ew + 6, eh + 8, 2, 0x0D0D10);
    g_mo.drop[0] = rrect(bx, 150, 6, 8, 12, 4, 0x7DD3FC);
    g_mo.drop[1] = rrect(bx, 18, 12, 8, 12, 4, 0x7DD3FC);
  } else if (thr == 100) {
    // KO: corpo acinzentado + olhos em X
    lv_obj_set_style_image_recolor(g_mo.img, lv_color_hex(0x6A6A74), 0);
    lv_obj_set_style_image_recolor_opa(g_mo.img, 190, 0);
    for (int i = 0; i < 2; i++) {
      g_moXPts[i * 2][0]     = { (lv_value_precise_t)(ex[i] - 2), (lv_value_precise_t)(ey - 1) };
      g_moXPts[i * 2][1]     = { (lv_value_precise_t)(ex[i] + ew + 2), (lv_value_precise_t)(ey + eh + 1) };
      g_moXPts[i * 2 + 1][0] = { (lv_value_precise_t)(ex[i] + ew + 2), (lv_value_precise_t)(ey - 1) };
      g_moXPts[i * 2 + 1][1] = { (lv_value_precise_t)(ex[i] - 2), (lv_value_precise_t)(ey + eh + 1) };
      for (int k = 0; k < 2; k++) {
        lv_obj_t *ln = lv_line_create(bx);
        lv_line_set_points(ln, g_moXPts[i * 2 + k], 2);
        lv_obj_set_style_line_width(ln, 4, 0);
        lv_obj_set_style_line_color(ln, lv_color_hex(C_BAD), 0);
        lv_obj_set_style_line_rounded(ln, true, 0);
        g_mo.xline[i * 2 + k] = ln;
      }
    }
  }

  // coluna de texto à direita
  lv_obj_t *win_l = mklabel(s, win == 0 ? TRS("JANELA DE 5 HORAS", "5-HOUR WINDOW")
                                        : TRS("JANELA SEMANAL", "WEEKLY WINDOW"),
                            &lv_font_montserrat_20, C_MUTED);
  lv_obj_set_pos(win_l, 240, 42);
  g_mo.pct = tlabel(s, &lv_font_montserrat_48, C_OK, 240, 70);
  const char *MSG[5] = {
    TRS("Comecando \xE2\x80\xA2 ritmo tranquilo",       "Just starting \xE2\x80\xA2 easy pace"),
    TRS("Metade da janela usada",                       "Half the window used"),
    TRS("Atencao \xE2\x80\xA2 uso alto",                "Heads up \xE2\x80\xA2 heavy usage"),
    TRS("Limite atingido \xE2\x80\xA2 aguarde o reset", "Limit reached \xE2\x80\xA2 wait for the reset"),
    TRS("Janela renovada! \xE2\x80\xA2 uso zerado",       "Window renewed! \xE2\x80\xA2 usage reset"),
  };
  int mi = (thr == 0) ? 4 : (thr == 25) ? 0 : (thr == 50) ? 1 : (thr == 70) ? 2 : 3;
  lv_obj_t *msg = mklabel(s, MSG[mi], &lv_font_montserrat_16, C_TEXT);
  lv_obj_set_pos(msg, 240, 148);
  lv_obj_set_width(msg, 232);
  lv_label_set_long_mode(msg, LV_LABEL_LONG_WRAP);

  for (int i = 0; i < NSEG; i++)
    g_mo.seg[i] = rrect(s, 240 + i * 11, 196, 8, 16, 2, C_TRACK);

  char e[32], b[48];
  fmt_eta(win == 0 ? g_usage.h5ResetEpoch : g_usage.d7ResetEpoch, e, sizeof(e));
  snprintf(b, sizeof(b), TRS("reseta em %s", "resets in %s"), e);
  lv_obj_t *eta = mklabel(s, b, &lv_font_montserrat_14, C_FAINT);
  lv_obj_set_pos(eta, 240, 228);

  lv_obj_t *hint = mklabel(s, TRS("toque para fechar", "tap to close"), &lv_font_montserrat_12, C_FAINT);
  lv_obj_set_pos(hint, 352, 296);
}

// Anima o momento (chamado a cada frame do loop enquanto o overlay existe).
static void moment_tick() {
  if (!g_mo.scrim) return;
  uint32_t t = millis() - g_mo.t0;

  // entrada: Clawd cai de cima com acomodação; depois o humor manda
  int y = g_mo.boxY, x = 36;
  if (t < 450) {
    float p = t / 450.0f;
    y = g_mo.boxY - (int)((1.0f - p) * (1.0f - p) * 60.0f);
  } else if (g_mo.thr == 0 || g_mo.thr == 25 || g_mo.thr == 50) {
    y = g_mo.boxY + (int)(4.0f * sinf((t - 450) / 260.0f));           // bounce feliz
  } else if (g_mo.thr == 70) {
    x = 36 + (((t / 70) % 2) ? 2 : -2);                                // treme
  } else if (g_mo.thr == 100) {
    y = g_mo.boxY + 6;                                                 // caído
  }
  lv_obj_set_pos(g_mo.box, x, y);

  // contador de % (200ms..1100ms) + medidor acendendo em sequência
  float p = (t < 200) ? 0 : (t > 1100 ? 1.0f : (t - 200) / 900.0f);
  float v = g_mo.fromPct + (g_mo.toPct - g_mo.fromPct) * p;
  char b[12]; snprintf(b, sizeof(b), "%d%%", (int)(v + 0.5f));
  lv_label_set_text(g_mo.pct, b);
  lv_obj_set_style_text_color(g_mo.pct, grad_color(v), 0);
  set_meter(g_mo.seg, v);

  // gotas de suor caindo em ciclo
  for (int i = 0; i < 2; i++) {
    if (!g_mo.drop[i]) continue;
    uint32_t c = (t + i * 450) % 900;
    lv_obj_set_y(g_mo.drop[i], (i ? 12 : 6) + (int)(c * 34 / 900));
    lv_obj_set_style_bg_opa(g_mo.drop[i], (lv_opa_t)(255 - c * 190 / 900), 0);
  }
  // anel vermelho piscando (100%)
  if (g_mo.ring)
    lv_obj_set_style_border_opa(g_mo.ring, ((t / 350) % 2) ? 190 : 30, 0);

  if (millis() > g_momentUntil) moment_close();
}

// Preenche todos os valores vindos do fetch (sem rebuild de tela).
static void refresh_ui_values() {
  if (g_state != ST_MAIN || !g_ui.agPct5) return;
  char b[96];

  // Agora: percentuais + medidores segmentados (cor desliza verde -> vermelho)
  snprintf(b, sizeof(b), "%d%%", (int)(g_usage.h5 + 0.5f)); lv_label_set_text(g_ui.agPct5, b);
  lv_obj_set_style_text_color(g_ui.agPct5, grad_color(g_usage.h5), 0);
  set_meter(g_ui.seg5, g_usage.h5);
  snprintf(b, sizeof(b), "%d%%", (int)(g_usage.d7 + 0.5f)); lv_label_set_text(g_ui.agPct7, b);
  lv_obj_set_style_text_color(g_ui.agPct7, grad_color(g_usage.d7), 0);
  set_meter(g_ui.seg7, g_usage.d7);

  set_chip(g_ui.agChip, overall_label(g_usage.statusOverall), status_color(g_usage.statusOverall));
  update_tok_row();
  or_refresh_ui();

  dash_tick();
}

// Atualiza o texto de status do cabeçalho (sem trocar de tela)
// O header nao tem mais texto de status ("atualizado ha Xmin" era redundante
// com a barra de refresh). O que sobrou de informacao — falhou ou nao — vai na
// cor da propria barra: coral normal, vermelha ate o proximo fetch OK.
static void set_hdr_status() {
  if (!g_ui.refBar) return;
  lv_obj_set_style_bg_color(g_ui.refBar, lv_color_hex(g_lastFetchOk ? C_ACCENT : C_BAD),
                            LV_PART_INDICATOR);
}
// Botão de refresh: só pede; a busca acontece em background no loop()
static void refresh_cb(lv_event_t *e) { (void)e; g_wantRefresh = true; }

static void ui_main() {
  lv_obj_t *scr = lv_screen_active();
  lv_obj_set_style_bg_color(scr, lv_color_hex(C_BG), 0);

  start_data_web();

  // Header: Clawd + logotipo (duplo toque em QUALQUER um = demo das animacoes),
  // botao de ATUALIZAR visivel no centro, engrenagem grande a direita.
  lv_obj_t *hIcon = lv_image_create(scr);
  lv_image_set_src(hIcon, &img_clawd_sm);
  lv_obj_set_pos(hIcon, 12, 10);               // 58x36 num header de 56px
  g_ui.hIcon = hIcon;
  lv_obj_t *hWord = lv_image_create(scr);
  g_ui.hWord = hWord;
  int logoEnd, badgeEnd;
  if (logo_present()) {
    // Slot de parceiro preenchido: sem wordmark; o logo fica centrado no header,
    // na mesma faixa vertical de 36px (ver partner_slot.h).
    lv_image_set_src(hWord, logo_dsc());
    lv_obj_align(hWord, LV_ALIGN_TOP_MID, 0, 10 + (36 - logo_h()) / 2);
    logoEnd = 12 + 58;                         // hotspot cobre so o Clawd
    badgeEnd = 240 - logo_w() / 2 - 8;
  } else {
    lv_image_set_src(hWord, &img_wordmark);
    lv_obj_set_pos(hWord, 80, 10);
    logoEnd = 80 + 78;                         // wordmark 78x36
    badgeEnd = 300;
    if (g_hasOr) {                             // nome do tile OpenRouter (sem logo de parceiro)
      g_ui.hOrName = lv_image_create(scr);     // nome "openrouter" 114x22 ao lado do simbolo
      lv_image_set_src(g_ui.hOrName, &img_or_text);
      lv_obj_set_pos(g_ui.hOrName, 62, 17);
      lv_obj_add_flag(g_ui.hOrName, LV_OBJ_FLAG_HIDDEN);
    }
  }

  lv_obj_t *logoSpot = lv_obj_create(scr);     // hotspot icone+nome (so demo)
  lv_obj_set_pos(logoSpot, 6, 2); lv_obj_set_size(logoSpot, logoEnd + 6 - 6, 52);
  lv_obj_set_style_bg_opa(logoSpot, 0, 0);
  lv_obj_set_style_border_width(logoSpot, 0, 0);
  lv_obj_clear_flag(logoSpot, LV_OBJ_FLAG_SCROLLABLE);
  lv_obj_add_flag(logoSpot, LV_OBJ_FLAG_CLICKABLE);
  lv_obj_add_event_cb(logoSpot, [](lv_event_t *e) {
    (void)e;
    static uint32_t lastClick = 0;             // duplo clique manual (9.2 nao tem nativo)
    static int di = 0;
    uint32_t now = millis();
    if (g_curTile != 0) return;                // demo e do Claude
    if (now - lastClick < 450) {
      static const int T[4] = {25, 50, 70, 100};
      show_moment((di / 4) % 2, T[di % 4]);
      di++;
      lastClick = 0;
    } else {
      lastClick = now;
    }
  }, LV_EVENT_CLICKED, NULL);

  // botao de atualizar a direita, colado na engrenagem (acao explicita; a busca
  // e bloqueante). Engrenagem ocupa x=396..474; este fica em 332..388.
  lv_obj_t *ref = mkbtn(scr, LV_SYMBOL_REFRESH, &lv_font_montserrat_20, C_SURFACE2, C_ACCENT);
  lv_obj_set_size(ref, 56, 40);
  lv_obj_set_ext_click_area(ref, 10);
  lv_obj_align(ref, LV_ALIGN_TOP_RIGHT, -92, 8);
  lv_obj_add_event_cb(ref, refresh_cb, LV_EVENT_CLICKED, NULL);


  // Badge da conta ativa, entre o logo e o botao de atualizar. O botao (mais
  // 10 px de ext_click_area) captura toque a partir de x=322; parar em 300
  // deixa folga para o toque "no badge" nao disparar o refresh. LONG_DOT corta
  // o rotulo que nao couber.
  // Com logo de parceiro (centrado) o badge fica entre o Clawd e o logo.
  const int acctX = (logoEnd + 8 > 138) ? logoEnd + 8 : 138;
  if (accountCount(g_accts) > 1 && badgeEnd - acctX >= 36) {
    char ab[ACCT_LBL_MAX + 1];
    snprintf(ab, sizeof(ab), "@%s", g_accts.label[g_accts.active]);
    lv_obj_t *acct = mklabel(scr, ab, &lv_font_montserrat_12, C_ACCENT);
    lv_obj_set_width(acct, badgeEnd - acctX);
    lv_label_set_long_mode(acct, LV_LABEL_LONG_DOT);
    lv_obj_align(acct, LV_ALIGN_TOP_LEFT, acctX, 22);
    g_ui.hAcct = acct;
  }

  lv_obj_t *gear = mkbtn(scr, LV_SYMBOL_SETTINGS, &lv_font_montserrat_22, C_SURFACE2, C_TEXT);
  lv_obj_set_size(gear, 78, 40);
  lv_obj_set_ext_click_area(gear, 16);
  lv_obj_align(gear, LV_ALIGN_TOP_RIGHT, -6, 8);
  lv_obj_add_event_cb(gear, nav_cb, LV_EVENT_CLICKED, (void *)(intptr_t)ST_SETTINGS);

  // Barra fina decrescente do próximo refresh (só indicador; o botão de
  // atualizar fica no centro do header — clique aqui causava refresh acidental)
  g_ui.refBar = lv_bar_create(scr);
  lv_obj_set_size(g_ui.refBar, 480, 3);
  lv_obj_set_pos(g_ui.refBar, 0, 56);
  lv_bar_set_range(g_ui.refBar, 0, 1000);
  lv_bar_set_value(g_ui.refBar, 1000, LV_ANIM_OFF);
  lv_obj_set_style_bg_color(g_ui.refBar, lv_color_hex(C_SURFACE), LV_PART_MAIN);
  lv_obj_set_style_bg_color(g_ui.refBar, lv_color_hex(C_ACCENT), LV_PART_INDICATOR);
  lv_obj_set_style_radius(g_ui.refBar, 0, LV_PART_MAIN);
  lv_obj_set_style_radius(g_ui.refBar, 0, LV_PART_INDICATOR);
  lv_obj_clear_flag(g_ui.refBar, LV_OBJ_FLAG_CLICKABLE);

  // Telas (swipe horizontal)
  g_ui.tv = lv_tileview_create(scr);
  lv_obj_set_pos(g_ui.tv, 0, 62);
  lv_obj_set_size(g_ui.tv, 480, 234);
  lv_obj_set_style_bg_opa(g_ui.tv, 0, 0);
  lv_obj_set_style_border_width(g_ui.tv, 0, 0);
  lv_obj_set_scrollbar_mode(g_ui.tv, LV_SCROLLBAR_MODE_OFF);
  const int nt = g_hasOr ? 2 : 1;
  for (int i = 0; i < nt; i++) {
    g_ui.tile[i] = lv_tileview_add_tile(g_ui.tv, i, 0, LV_DIR_HOR);
    tile_setup(g_ui.tile[i]);
  }
  build_tile_agora(g_ui.tile[0]);
  if (g_hasOr) build_tile_or(g_ui.tile[1]);
  lv_obj_add_event_cb(g_ui.tv, on_tile_changed, LV_EVENT_VALUE_CHANGED, NULL);

  // Dots (objetos; o ativo vira pílula) — so com mais de um tile
  for (int i = 0; i < nt && nt > 1; i++) {
    g_ui.dots[i] = lv_obj_create(scr);
    lv_obj_set_size(g_ui.dots[i], 8, 8);
    lv_obj_set_style_radius(g_ui.dots[i], 4, 0);
    lv_obj_set_style_bg_color(g_ui.dots[i], lv_color_hex(C_BORDER), 0);
    lv_obj_set_style_border_width(g_ui.dots[i], 0, 0);
    lv_obj_clear_flag(g_ui.dots[i], LV_OBJ_FLAG_SCROLLABLE);
    lv_obj_align(g_ui.dots[i], LV_ALIGN_BOTTOM_MID, (int)((i - (nt - 1) / 2.0f) * 18), -4);
  }

  refresh_ui_values();
  on_tile_changed(NULL);
}

// ============================================================
// Tela: settings (lista rolável; linhas >=44px de toque)
// ============================================================
static bool g_wipeArmed = false;
static bool g_orDelArmed = false;
static lv_obj_t *g_orLbl = nullptr;
static lv_obj_t *g_briLbl = nullptr, *g_wipeLbl = nullptr, *g_pollLbl = nullptr,
                *g_tzLbl = nullptr, *g_slideLbl = nullptr;
static const int POLL_OPTS[] = {15, 30, 60, 120, 300};
#define NPOLL_OPTS (int)(sizeof(POLL_OPTS) / sizeof(POLL_OPTS[0]))
static const int TZ_OPTS[] = {-3, -4, -5, -6, -7, -8, -2, -1, 0, 1, 2, 3};
#define NTZ ((int)(sizeof(TZ_OPTS) / sizeof(TZ_OPTS[0])))

static lv_obj_t *g_wkMascLbl = nullptr, *g_otaSetLbl = nullptr, *g_dimLbl = nullptr, *g_nightLbl = nullptr;
static void dim_txt(char *out, size_t sz) {
  if (g_dimMin) snprintf(out, sz, TRS(LV_SYMBOL_EYE_CLOSE "  Escurecer: apos %d min",
                                      LV_SYMBOL_EYE_CLOSE "  Dim: after %d min"), g_dimMin);
  else snprintf(out, sz, "%s", TRS(LV_SYMBOL_EYE_CLOSE "  Escurecer: desligado",
                                   LV_SYMBOL_EYE_CLOSE "  Dim: off"));
}
static void night_txt(char *out, size_t sz) {
  if (g_nightOn) snprintf(out, sz, TRS(LV_SYMBOL_POWER "  Modo noite: %02dh-%02dh",
                                       LV_SYMBOL_POWER "  Night mode: %02dh-%02dh"), g_nightFrom, g_nightTo);
  else snprintf(out, sz, "%s", TRS(LV_SYMBOL_POWER "  Modo noite: desligado (horario no painel web)",
                                   LV_SYMBOL_POWER "  Night mode: off (hours in web panel)"));
}
static void week_masc_txt(char *out, size_t sz) {
  const char *n[4] = {TRS("desligado", "off"), "Clawd", TRS("rodizio", "rotation"), TRS("humor", "mood")};
  snprintf(out, sz, TRS(LV_SYMBOL_IMAGE "  Mascote semanal: %s", LV_SYMBOL_IMAGE "  Weekly mascot: %s"),
           n[g_weekMasc]);
}

static int g_acctDelArmed = -1;

static void settings_action_cb(lv_event_t *e) {
  int act = (int)(intptr_t)lv_event_get_user_data(e);
  switch (act) {
    case 0: request_state(ST_LOADING); break;          // atualizar
    case 1: g_onboarding = false; request_state(ST_WIFI); break;
    case 2:                                            // trocar token
      g_tokenTargetSlot = g_accts.active;
      g_pendingLabel[0] = 0;
      request_state(ST_TOKEN);
      break;
    case 3:                                            // brilho
      g_briIdx = (g_briIdx + 1) % 3; g_prefs.putInt("bri", g_briIdx); apply_brightness();
      if (g_briLbl) {
        const char *n[3] = {TRS("baixo", "low"), TRS("medio", "medium"), TRS("alto", "high")};
        char m[40]; snprintf(m, sizeof(m), TRS(LV_SYMBOL_EYE_OPEN "  Brilho: %s",
                                               LV_SYMBOL_EYE_OPEN "  Brightness: %s"), n[g_briIdx]);
        lv_label_set_text(g_briLbl, m);
      }
      break;
    case 4:                                            // apagar tudo (2 toques)
      if (!g_wipeArmed) {
        g_wipeArmed = true;
        if (g_wipeLbl) lv_label_set_text(g_wipeLbl, TRS(LV_SYMBOL_TRASH "  Toque de novo p/ confirmar",
                                                        LV_SYMBOL_TRASH "  Tap again to confirm"));
      } else {
        g_wipeArmed = false;
        factory_reset();
        request_state(ST_WIFI);
      }
      break;
    case 5: request_state(ST_MAIN); break;             // voltar
    case 6: {                                          // intervalo de atualização
      int idx = 0;
      for (int i = 0; i < NPOLL_OPTS; i++) if (POLL_OPTS[i] == g_pollSec) idx = i;
      g_pollSec = POLL_OPTS[(idx + 1) % NPOLL_OPTS];
      g_prefs.putInt("poll", g_pollSec);
      if (g_pollLbl) {
        char m[40];
        if (g_pollSec < 60) snprintf(m, sizeof(m), TRS(LV_SYMBOL_LOOP "  Atualizar: %ds",
                                                       LV_SYMBOL_LOOP "  Refresh: %ds"), g_pollSec);
        else snprintf(m, sizeof(m), TRS(LV_SYMBOL_LOOP "  Atualizar: %dmin",
                                        LV_SYMBOL_LOOP "  Refresh: %dmin"), g_pollSec / 60);
        lv_label_set_text(g_pollLbl, m);
      }
      break;
    }
    case 7: {                                          // fuso horário (GMT)
      int idx = 0;
      for (int i = 0; i < NTZ; i++) if (TZ_OPTS[i] == g_tzOffset) idx = i;
      g_tzOffset = TZ_OPTS[(idx + 1) % NTZ];
      g_prefs.putInt("tz", g_tzOffset);
      apply_tz();
      if (g_tzLbl) {
        char m[40];
        snprintf(m, sizeof(m), TRS(LV_SYMBOL_GPS "  Fuso: GMT%+d",
                                   LV_SYMBOL_GPS "  Timezone: GMT%+d"), g_tzOffset);
        lv_label_set_text(g_tzLbl, m);
      }
      break;
    }
    case 8: {                                          // slideshow: off -> 5 -> 10 -> 15 -> 30 -> off
      static const int SL[5] = {0, 5, 10, 15, 30};
      int idx = 0;
      for (int i = 0; i < 5; i++) if (SL[i] == g_slideSec) idx = i;
      g_slideSec = SL[(idx + 1) % 5];
      g_prefs.putInt("slide", g_slideSec);
      if (g_slideLbl) {
        char m[48];
        if (g_slideSec) snprintf(m, sizeof(m), LV_SYMBOL_PLAY "  Slideshow: %ds", g_slideSec);
        else            snprintf(m, sizeof(m), "%s", TRS(LV_SYMBOL_PLAY "  Slideshow: desligado",
                                                         LV_SYMBOL_PLAY "  Slideshow: off"));
        lv_label_set_text(g_slideLbl, m);
      }
      break;
    }
    case 9:                                            // idioma / language
      g_lang ^= 1;
      g_prefs.putInt("lang", g_lang);
      request_state(ST_SETTINGS);                      // redesenha tudo no novo idioma
      break;
    case 10: request_state(ST_ABOUT); break;           // sobre / about
    case 11: g_acctDelArmed = -1; request_state(ST_ACCOUNTS); break;
    case 12:                                           // mascote semanal: Clawd -> rodizio -> humor -> off
      g_weekMasc = (g_weekMasc + 1) % 4;
      g_prefs.putInt("wmasc", g_weekMasc);
      if (g_wkMascLbl) { char m[64]; week_masc_txt(m, sizeof(m)); lv_label_set_text(g_wkMascLbl, m); }
      break;
    case 14: {                                         // escurecer: off -> 1 -> 5 -> 10 -> 30 -> off
      static const int DM[5] = {0, 1, 5, 10, 30};
      int idx = 0;
      for (int i = 0; i < 5; i++) if (DM[i] == g_dimMin) idx = i;
      g_dimMin = DM[(idx + 1) % 5];
      g_prefs.putInt("dim", g_dimMin);
      if (g_dimLbl) { char m[64]; dim_txt(m, sizeof(m)); lv_label_set_text(g_dimLbl, m); }
      break;
    }
    case 15:                                           // modo noite liga/desliga
      g_nightOn = !g_nightOn;
      g_prefs.putBool("night", g_nightOn);
      if (g_nightLbl) { char m[80]; night_txt(m, sizeof(m)); lv_label_set_text(g_nightLbl, m); }
      break;
    case 16:                                           // OpenRouter: conectar / remover (2 toques)
      if (!g_hasOr) {
        g_orEntry = true;
        request_state(ST_TOKEN);
      } else if (!g_orDelArmed) {
        g_orDelArmed = true;
        if (g_orLbl) lv_label_set_text(g_orLbl, TRS(LV_SYMBOL_CLOSE "  OpenRouter: toque de novo p/ remover",
                                                   LV_SYMBOL_CLOSE "  OpenRouter: tap again to remove"));
      } else {
        or_remove();
        request_state(ST_SETTINGS);
      }
      break;
    case 13:                                           // abre janela de OTA (5 min)
      g_otaUntil = millis() + OTA_WINDOW_MS;
      if (!g_otaUntil) g_otaUntil = 1;                 // 0 e o sentinela de "fechado"
      Serial.println("[OTA] janela aberta por 5 min");
      if (g_otaSetLbl) {
        char m[80];
        snprintf(m, sizeof(m), TRS(LV_SYMBOL_UPLOAD "  OTA aberto 5 min: %s/update",
                                   LV_SYMBOL_UPLOAD "  OTA open 5 min: %s/update"),
                 WiFi.localIP().toString().c_str());
        lv_label_set_text(g_otaSetLbl, m);
      }
      break;
  }
}
static void add_setting_row(lv_obj_t *p, const char *txt, int act, uint32_t fg, lv_obj_t **out) {
  lv_obj_t *b = lv_button_create(p);
  lv_obj_set_size(b, 444, 44);
  lv_obj_set_style_bg_color(b, lv_color_hex(C_SURFACE), 0);
  lv_obj_set_style_radius(b, 12, 0);
  lv_obj_set_style_shadow_width(b, 0, 0);
  lv_obj_t *l = mklabel(b, txt, &lv_font_montserrat_16, fg);
  lv_obj_align(l, LV_ALIGN_LEFT_MID, 8, 0);
  lv_obj_add_event_cb(b, settings_action_cb, LV_EVENT_CLICKED, (void *)(intptr_t)act);
  if (out) *out = l;
}
static void ui_settings() {
  lv_obj_t *scr = lv_screen_active();
  g_wipeArmed = false;
  g_orDelArmed = false;
  start_data_web();
  lv_obj_t *title = mklabel(scr, TRS("Ajustes", "Settings"), &lv_font_montserrat_20, C_TEXT);
  lv_obj_align(title, LV_ALIGN_TOP_LEFT, 14, 10);

  lv_obj_t *bk = mkbtn(scr, TRS(LV_SYMBOL_LEFT " Voltar", LV_SYMBOL_LEFT " Back"),
                       &lv_font_montserrat_14, C_SURFACE2, C_MUTED);
  lv_obj_set_size(bk, 100, 32);
  lv_obj_set_ext_click_area(bk, 6);
  lv_obj_align(bk, LV_ALIGN_TOP_RIGHT, -12, 6);
  lv_obj_add_event_cb(bk, nav_cb, LV_EVENT_CLICKED, (void *)(intptr_t)(g_usage.ok ? ST_MAIN : ST_SETTINGS));

  // lista rolável
  lv_obj_t *lst = lv_obj_create(scr);
  lv_obj_set_pos(lst, 8, 44);
  lv_obj_set_size(lst, 464, 268);
  lv_obj_set_style_bg_opa(lst, 0, 0);
  lv_obj_set_style_border_width(lst, 0, 0);
  lv_obj_set_style_pad_all(lst, 0, 0);
  lv_obj_set_style_pad_row(lst, 8, 0);
  lv_obj_set_flex_flow(lst, LV_FLEX_FLOW_COLUMN);
  lv_obj_set_scroll_dir(lst, LV_DIR_VER);
  lv_obj_set_scrollbar_mode(lst, LV_SCROLLBAR_MODE_AUTO);

  const char *n[3] = {TRS("baixo", "low"), TRS("medio", "medium"), TRS("alto", "high")};
  char bri[40]; snprintf(bri, sizeof(bri), TRS(LV_SYMBOL_EYE_OPEN "  Brilho: %s",
                                               LV_SYMBOL_EYE_OPEN "  Brightness: %s"), n[g_briIdx]);
  char pollTxt[40];
  if (g_pollSec < 60) snprintf(pollTxt, sizeof(pollTxt), TRS(LV_SYMBOL_LOOP "  Atualizar: %ds",
                                                             LV_SYMBOL_LOOP "  Refresh: %ds"), g_pollSec);
  else                snprintf(pollTxt, sizeof(pollTxt), TRS(LV_SYMBOL_LOOP "  Atualizar: %dmin",
                                                             LV_SYMBOL_LOOP "  Refresh: %dmin"), g_pollSec / 60);
  char tzTxt[40]; snprintf(tzTxt, sizeof(tzTxt), TRS(LV_SYMBOL_GPS "  Fuso: GMT%+d",
                                                     LV_SYMBOL_GPS "  Timezone: GMT%+d"), g_tzOffset);
  char slideTxt[48];
  if (g_slideSec) snprintf(slideTxt, sizeof(slideTxt), LV_SYMBOL_PLAY "  Slideshow: %ds", g_slideSec);
  else            snprintf(slideTxt, sizeof(slideTxt), "%s", TRS(LV_SYMBOL_PLAY "  Slideshow: desligado",
                                                                 LV_SYMBOL_PLAY "  Slideshow: off"));

  add_setting_row(lst, TRS(LV_SYMBOL_REFRESH "  Atualizar agora",
                           LV_SYMBOL_REFRESH "  Refresh now"),   0, C_TEXT, nullptr);
  add_setting_row(lst, pollTxt,                                  6, C_TEXT, &g_pollLbl);
  add_setting_row(lst, slideTxt,                                 8, C_TEXT, &g_slideLbl);
  char wkTxt[64]; week_masc_txt(wkTxt, sizeof(wkTxt));
  add_setting_row(lst, wkTxt,                                   12, C_TEXT, &g_wkMascLbl);
  add_setting_row(lst, TRS(LV_SYMBOL_LIST "  Idioma: Portugues",
                           LV_SYMBOL_LIST "  Language: English"), 9, C_TEXT, nullptr);
  add_setting_row(lst, tzTxt,                                    7, C_TEXT, &g_tzLbl);
  add_setting_row(lst, bri,                                      3, C_TEXT, &g_briLbl);
  char dimTxt[64]; dim_txt(dimTxt, sizeof(dimTxt));
  add_setting_row(lst, dimTxt,                                  14, C_TEXT, &g_dimLbl);
  char nightTxt[80]; night_txt(nightTxt, sizeof(nightTxt));
  add_setting_row(lst, nightTxt,                                15, C_TEXT, &g_nightLbl);
  add_setting_row(lst, TRS(LV_SYMBOL_WIFI "  Configurar WiFi",
                           LV_SYMBOL_WIFI "  Configure WiFi"),   1, C_TEXT, nullptr);
  char acctTxt[64];
  snprintf(acctTxt, sizeof(acctTxt), TRS(LV_SYMBOL_DIRECTORY "  Contas: %s (%d/%d)",
                                         LV_SYMBOL_DIRECTORY "  Accounts: %s (%d/%d)"),
           g_accts.label[g_accts.active], accountCount(g_accts), ACCT_MAX);
  add_setting_row(lst, acctTxt,                                 11, C_TEXT, nullptr);
  add_setting_row(lst, g_hasOr ? TRS(LV_SYMBOL_OK "  OpenRouter: conectado", LV_SYMBOL_OK "  OpenRouter: connected")
                               : TRS(LV_SYMBOL_PLUS "  OpenRouter: conectar", LV_SYMBOL_PLUS "  OpenRouter: connect"),
                  16, C_TEXT, &g_orLbl);
  add_setting_row(lst, TRS(LV_SYMBOL_KEYBOARD "  Trocar token",
                           LV_SYMBOL_KEYBOARD "  Change token"), 2, C_TEXT, nullptr);
  add_setting_row(lst, TRS(LV_SYMBOL_UPLOAD "  Atualizar firmware (WiFi)",
                           LV_SYMBOL_UPLOAD "  Update firmware (WiFi)"), 13, C_TEXT, &g_otaSetLbl);
  add_setting_row(lst, TRS(LV_SYMBOL_FILE "  Sobre",
                           LV_SYMBOL_FILE "  About"),           10, C_TEXT, nullptr);
  add_setting_row(lst, TRS(LV_SYMBOL_TRASH "  Apagar tudo",
                           LV_SYMBOL_TRASH "  Erase everything"), 4, C_BAD, &g_wipeLbl);
}

static void acct_switch_cb(lv_event_t *e) {
  int slot = (int)(intptr_t)lv_event_get_user_data(e);
  g_acctDelArmed = -1;
  if (slot == g_accts.active) return;
  if (!switch_account(slot)) request_state(ST_ACCOUNTS);
}
static void acct_del_cb(lv_event_t *e) {
  int slot = (int)(intptr_t)lv_event_get_user_data(e);
  if (accountCount(g_accts) <= 1) return;
  if (g_acctDelArmed != slot) {
    g_acctDelArmed = slot;
    request_state(ST_ACCOUNTS);
    return;
  }
  g_acctDelArmed = -1;
  bool wasActive = (slot == g_accts.active);
  accountRemove(g_prefs, g_accts, slot);
  if (wasActive) {
    EncryptedBlob b; char tok[200];
    if (accountLoadBlob(g_prefs, g_accts.active, b) &&
        decryptToken(b, g_sessionPin, tok, sizeof(tok))) {
      g_blob = b;
      strlcpy(g_token, tok, sizeof(g_token));
      memset(tok, 0, sizeof(tok));
      memset(&g_tok, 0, sizeof(g_tok));
      memset(&g_usage, 0, sizeof(g_usage));
      request_state(ST_LOADING);
      return;
    }
  }
  request_state(ST_ACCOUNTS);
}
static void acct_add_cb(lv_event_t *e) {
  (void)e;
  int slot = accountFirstFree(g_accts);
  if (slot < 0) return;
  g_tokenTargetSlot = slot;
  g_pendingLabel[0] = 0;
  request_state(ST_TOKEN);
}
static int g_renameSlot = -1;
static lv_obj_t *g_nameTa = nullptr;

static void acct_edit_cb(lv_event_t *e) {
  g_renameSlot = (int)(intptr_t)lv_event_get_user_data(e);
  g_acctDelArmed = -1;
  request_state(ST_ACCT_NAME);
}
static void acct_name_kb_cb(lv_event_t *e) {
  lv_event_code_t code = lv_event_get_code(e);
  if (code == LV_EVENT_READY) {
    accountSetLabel(g_prefs, g_accts, g_renameSlot, lv_textarea_get_text(g_nameTa));
    request_state(ST_ACCOUNTS);
  } else if (code == LV_EVENT_CANCEL) {
    request_state(ST_ACCOUNTS);
  }
}

static void ui_account_name() {
  if (g_renameSlot < 0 || g_renameSlot >= ACCT_MAX || !g_accts.used[g_renameSlot]) {
    request_state(ST_ACCOUNTS);
    return;
  }
  lv_obj_t *scr = lv_screen_active();

  lv_obj_t *title = mklabel(scr, TRS("Renomear conta", "Rename account"),
                            &lv_font_montserrat_20, C_TEXT);
  lv_obj_align(title, LV_ALIGN_TOP_LEFT, 14, 10);

  lv_obj_t *bk = mkbtn(scr, TRS(LV_SYMBOL_LEFT " Voltar", LV_SYMBOL_LEFT " Back"),
                       &lv_font_montserrat_14, C_SURFACE2, C_MUTED);
  lv_obj_set_size(bk, 100, 32);
  lv_obj_set_ext_click_area(bk, 6);
  lv_obj_align(bk, LV_ALIGN_TOP_RIGHT, -12, 6);
  lv_obj_add_event_cb(bk, nav_cb, LV_EVENT_CLICKED, (void *)(intptr_t)ST_ACCOUNTS);

  g_nameTa = lv_textarea_create(scr);
  lv_textarea_set_one_line(g_nameTa, true);
  lv_textarea_set_max_length(g_nameTa, ACCT_LBL_MAX - 1);
  lv_textarea_set_text(g_nameTa, g_accts.label[g_renameSlot]);
  lv_textarea_set_placeholder_text(g_nameTa, TRS("rotulo (ex.: Pessoal, Trabalho)",
                                                 "label (e.g. Personal, Work)"));
  lv_obj_set_size(g_nameTa, 452, 44);
  lv_obj_align(g_nameTa, LV_ALIGN_TOP_MID, 0, 52);

  lv_obj_t *kb = lv_keyboard_create(scr);
  lv_keyboard_set_textarea(kb, g_nameTa);
  lv_obj_add_event_cb(kb, acct_name_kb_cb, LV_EVENT_ALL, NULL);
}

static void ui_accounts() {
  lv_obj_t *scr = lv_screen_active();
  start_data_web();

  lv_obj_t *title = mklabel(scr, TRS("Contas", "Accounts"), &lv_font_montserrat_20, C_TEXT);
  lv_obj_align(title, LV_ALIGN_TOP_LEFT, 14, 10);

  lv_obj_t *bk = mkbtn(scr, TRS(LV_SYMBOL_LEFT " Voltar", LV_SYMBOL_LEFT " Back"),
                       &lv_font_montserrat_14, C_SURFACE2, C_MUTED);
  lv_obj_set_size(bk, 100, 32);
  lv_obj_set_ext_click_area(bk, 6);
  lv_obj_align(bk, LV_ALIGN_TOP_RIGHT, -12, 6);
  lv_obj_add_event_cb(bk, nav_cb, LV_EVENT_CLICKED, (void *)(intptr_t)ST_SETTINGS);

  lv_obj_t *lst = lv_obj_create(scr);
  lv_obj_set_pos(lst, 8, 44);
  lv_obj_set_size(lst, 464, 240);
  lv_obj_set_style_bg_opa(lst, 0, 0);
  lv_obj_set_style_border_width(lst, 0, 0);
  lv_obj_set_style_pad_all(lst, 0, 0);
  lv_obj_set_style_pad_row(lst, 8, 0);
  lv_obj_set_flex_flow(lst, LV_FLEX_FLOW_COLUMN);
  lv_obj_set_scroll_dir(lst, LV_DIR_VER);
  lv_obj_set_scrollbar_mode(lst, LV_SCROLLBAR_MODE_AUTO);

  bool canDelete = accountCount(g_accts) > 1;
  for (int i = 0; i < ACCT_MAX; i++) {
    if (!g_accts.used[i]) continue;
    bool active = (i == g_accts.active);

    lv_obj_t *row = lv_obj_create(lst);
    lv_obj_set_size(row, 444, 44);
    no_box(row);

    lv_obj_t *b = lv_button_create(row);
    lv_obj_set_size(b, canDelete ? 324 : 384, 44);
    lv_obj_set_pos(b, 0, 0);
    lv_obj_set_style_bg_color(b, lv_color_hex(C_SURFACE), 0);
    lv_obj_set_style_radius(b, 12, 0);
    lv_obj_set_style_shadow_width(b, 0, 0);
    char txt[40];
    snprintf(txt, sizeof(txt), "%s%s", g_accts.label[i],
             active ? TRS("  \xE2\x80\xA2  ativa", "  \xE2\x80\xA2  active") : "");
    lv_obj_t *l = mklabel(b, txt, &lv_font_montserrat_16, active ? C_ACCENT : C_TEXT);
    lv_obj_align(l, LV_ALIGN_LEFT_MID, 8, 0);
    lv_obj_add_event_cb(b, acct_switch_cb, LV_EVENT_CLICKED, (void *)(intptr_t)i);

    lv_obj_t *ed = lv_button_create(row);
    lv_obj_set_size(ed, 52, 44);
    lv_obj_set_pos(ed, canDelete ? 332 : 392, 0);
    lv_obj_set_style_bg_color(ed, lv_color_hex(C_SURFACE2), 0);
    lv_obj_set_style_radius(ed, 12, 0);
    lv_obj_set_style_shadow_width(ed, 0, 0);
    lv_obj_center(mklabel(ed, LV_SYMBOL_EDIT, &lv_font_montserrat_16, C_MUTED));
    lv_obj_add_event_cb(ed, acct_edit_cb, LV_EVENT_CLICKED, (void *)(intptr_t)i);

    if (canDelete) {
      bool armed = (g_acctDelArmed == i);
      lv_obj_t *d = lv_button_create(row);
      lv_obj_set_size(d, 52, 44);
      lv_obj_set_pos(d, 392, 0);
      lv_obj_set_style_bg_color(d, lv_color_hex(armed ? C_BAD : C_SURFACE2), 0);
      lv_obj_set_style_radius(d, 12, 0);
      lv_obj_set_style_shadow_width(d, 0, 0);
      lv_obj_center(mklabel(d, armed ? LV_SYMBOL_WARNING : LV_SYMBOL_TRASH,
                            &lv_font_montserrat_16, armed ? C_BG : C_MUTED));
      lv_obj_add_event_cb(d, acct_del_cb, LV_EVENT_CLICKED, (void *)(intptr_t)i);
    }
  }

  if (accountFirstFree(g_accts) >= 0) {
    lv_obj_t *add = lv_button_create(lst);
    lv_obj_set_size(add, 444, 44);
    lv_obj_set_style_bg_color(add, lv_color_hex(C_SURFACE2), 0);
    lv_obj_set_style_radius(add, 12, 0);
    lv_obj_set_style_shadow_width(add, 0, 0);
    lv_obj_t *al = mklabel(add, TRS(LV_SYMBOL_PLUS "  Adicionar conta",
                                    LV_SYMBOL_PLUS "  Add account"),
                           &lv_font_montserrat_16, C_ACCENT);
    lv_obj_align(al, LV_ALIGN_LEFT_MID, 8, 0);
    lv_obj_add_event_cb(add, acct_add_cb, LV_EVENT_CLICKED, NULL);
  }

  lv_obj_t *hint = mklabel(scr, TRS("So a conta ativa e consultada na API (as outras ficam dormentes).",
                                    "Only the active account is polled (the others stay dormant)."),
                           &lv_font_montserrat_12, C_FAINT);
  lv_obj_set_width(hint, 452);
  lv_label_set_long_mode(hint, LV_LABEL_LONG_WRAP);
  lv_obj_align(hint, LV_ALIGN_BOTTOM_LEFT, 14, -8);
}

// ============================================================
// Tela: sobre / about
// ============================================================
static void ui_about() {
  lv_obj_t *scr = lv_screen_active();
  start_data_web();

  lv_obj_t *bk = mkbtn(scr, TRS(LV_SYMBOL_LEFT " Voltar", LV_SYMBOL_LEFT " Back"),
                       &lv_font_montserrat_14, C_SURFACE2, C_MUTED);
  lv_obj_set_size(bk, 100, 32);
  lv_obj_set_ext_click_area(bk, 6);
  lv_obj_align(bk, LV_ALIGN_TOP_RIGHT, -12, 6);
  lv_obj_add_event_cb(bk, nav_cb, LV_EVENT_CLICKED, (void *)(intptr_t)ST_SETTINGS);

  lv_obj_t *mark = build_claude_mark(scr);
  lv_obj_align(mark, LV_ALIGN_TOP_MID, 0, 0);

  lv_obj_t *t = mklabel(scr, "Claude Usage Stick", &lv_font_montserrat_22, C_TEXT);
  lv_obj_align(t, LV_ALIGN_TOP_MID, 0, 94);

  char v[64];
  snprintf(v, sizeof(v), "v" FW_VERSION " \xE2\x80\xA2 ESP32-S3 \xE2\x80\xA2 LVGL 9.2");
  lv_obj_t *ver = mklabel(scr, v, &lv_font_montserrat_12, C_FAINT);
  lv_obj_align(ver, LV_ALIGN_TOP_MID, 0, 122);
  if (logo_present()) {                // logo do parceiro ao lado da versao
    lv_obj_t *pl = lv_image_create(scr);
    lv_image_set_src(pl, logo_dsc());
    lv_obj_align_to(pl, ver, LV_ALIGN_OUT_RIGHT_MID, 12, 0);
  }

  lv_obj_t *d = mklabel(scr, TRS("Medidor de uso do Claude Code em tempo real: "
                                 "janelas de 5h e semanal direto da API da Anthropic.",
                                 "Real-time Claude Code usage meter: "
                                 "5-hour and weekly windows straight from the Anthropic API."),
                        &lv_font_montserrat_14, C_MUTED);
  lv_obj_set_width(d, 420);
  lv_obj_set_style_text_align(d, LV_TEXT_ALIGN_CENTER, 0);
  lv_label_set_long_mode(d, LV_LABEL_LONG_WRAP);
  lv_obj_align(d, LV_ALIGN_TOP_MID, 0, 146);

  lv_obj_t *h = mklabel(scr, TRS("Tela: Guition JC4832W535 \xE2\x80\xA2 IPS 3.5\" 480x320 touch (AXS15231B)",
                                 "Display: Guition JC4832W535 \xE2\x80\xA2 3.5\" IPS 480x320 touch (AXS15231B)"),
                        &lv_font_montserrat_12, C_FAINT);
  lv_obj_align(h, LV_ALIGN_TOP_MID, 0, 200);

  lv_obj_t *devCap = mklabel(scr, TRS("Desenvolvido por", "Developed by"), &lv_font_montserrat_12, C_FAINT);
  lv_obj_align(devCap, LV_ALIGN_TOP_MID, 0, 234);
  lv_obj_t *dev = mklabel(scr, "Benevid Felix", &lv_font_montserrat_18, C_TEXT);
  lv_obj_align(dev, LV_ALIGN_TOP_MID, 0, 254);
  lv_obj_t *mail = mklabel(scr, "benevid@gmail.com", &lv_font_montserrat_14, C_ACCENT);
  lv_obj_align(mail, LV_ALIGN_TOP_MID, 0, 282);
}

// ============================================================
// Navegação genérica
// ============================================================
static void nav_cb(lv_event_t *e) {
  State s = (State)(intptr_t)lv_event_get_user_data(e);
  request_state(s);
}

// ============================================================
// Render do estado atual
// ============================================================
static void render_state() {
  g_state = g_pending;
  if (g_state != ST_TOKEN) g_orEntry = false;
  stop_web();                                 // cada tela sobe o servidor que precisa
  moment_close();                             // overlay vive em lv_layer_top
  lv_obj_clean(lv_layer_top());
  g_otaLbl = nullptr;                    // vivia na layer_top
  // invalida ponteiros vivos antes de destruir a tela antiga
  memset(&g_ui, 0, sizeof(g_ui));
  g_mascN = 0;
  g_pinDots = g_pinMsg = nullptr;
  g_tokMsg = nullptr;
  g_nameTa = nullptr;
  g_briLbl = g_wipeLbl = g_pollLbl = g_tzLbl = g_slideLbl = g_wkMascLbl = g_otaSetLbl = g_dimLbl = g_nightLbl = g_orLbl = nullptr;

  lv_obj_clean(lv_screen_active());
  lv_obj_set_style_bg_color(lv_screen_active(), lv_color_hex(C_BG), 0);
  lv_obj_set_style_bg_opa(lv_screen_active(), LV_OPA_COVER, 0);

  switch (g_state) {
    case ST_PIN:
    case ST_SETUP_PIN: ui_pin(); break;
    case ST_WIFI:      ui_wifi(); break;
    case ST_TOKEN:     ui_token(); break;
    case ST_LOADING:   ui_loading(g_wifi.isConnected() ? g_wifi.getSSID().c_str()
                                                       : TRS("conectando WiFi", "connecting WiFi")); break;
    case ST_MAIN:      ui_main(); break;
    case ST_SETTINGS:  ui_settings(); break;
    case ST_ACCOUNTS:  ui_accounts(); break;
    case ST_ACCT_NAME: ui_account_name(); break;
    case ST_ABOUT:     ui_about(); break;
    case ST_ERROR:     ui_message(TRS("Falha", "Failed"),
                                  g_usage.error[0] ? g_usage.error : TRS("sem dados", "no data"), C_BAD); break;
    default: break;
  }
}

// ============================================================
// Tempo (NTP) e ciclo de dados
// ============================================================
static void apply_tz() { configTime(g_tzOffset * 3600, 0, NTP_SERVER_1, NTP_SERVER_2); }
static void ensure_time() {
  if (g_timeInit || !g_wifi.isConnected()) return;
  apply_tz();
  g_timeInit = true;
  Serial.println("[NTP] sync iniciado");
}

// Heap livre + maior bloco contiguo. O handshake TLS precisa de ~45KB contiguos:
// heap total alto com maior bloco pequeno (fragmentacao) da o mesmo http_-1.
static void log_mem(const char *tag) {
  lv_mem_monitor_t m;
  lv_mem_monitor(&m);
  Serial.printf("[MEM] %s heap=%u maior=%u psram=%u lvgl=%u/%u frag=%u%%\n", tag,
                (unsigned)ESP.getFreeHeap(),
                (unsigned)heap_caps_get_largest_free_block(MALLOC_CAP_INTERNAL | MALLOC_CAP_8BIT),
                (unsigned)ESP.getFreePsram(),
                (unsigned)(m.total_size - m.free_size), (unsigned)m.total_size,
                (unsigned)m.frag_pct);
}

// Primeiro load (mostra a tela de carregamento). Vai p/ ST_MAIN ou ST_ERROR.
static void do_refresh() {
  ensure_time();
  bool ok = fetchUsage(g_token, g_usage);
  if (ok) {
    g_lastOkMs = millis(); g_lastFetchOk = true;
    check_thresholds();
  } else g_lastFetchOk = false;
  or_poll();
  apiClose();                   // libera o contexto TLS (~40KB) entre polls
  log_mem("refresh");
  g_lastPollMs = millis();
  request_state(ok ? ST_MAIN : ST_ERROR);
}

// Atualização EM BACKGROUND: não troca de tela; mantém o dashboard e os dados
// antigos se falhar. A chamada à API é bloqueante (~1-2s), então mostra
// "atualizando..." no cabeçalho durante a busca.
static void bg_refresh() {
  // Sem WiFi nao se tenta reconectar aqui: autoConnect() bloqueia ate 8s POR rede
  // salva (24s) com o LVGL parado. Quem reconecta e o g_wifi.maintain() do loop().
  if (!g_wifi.isConnected()) { g_lastFetchOk = false; g_lastPollMs = millis(); return; }
  ensure_time();
  g_refreshing = true; set_hdr_status(); lv_refr_now(NULL);
  UsageData u = {};
  bool ok = fetchUsage(g_token, u);
  if (ok) {
    g_usage = u; g_lastOkMs = millis(); g_lastFetchOk = true;
    check_thresholds();
  } else g_lastFetchOk = false;
  or_poll();
  apiClose();                   // libera o contexto TLS (~40KB) entre polls
  log_mem("bg_refresh");
  g_refreshing = false;
  g_lastPollMs = millis();
  refresh_ui_values();                    // in-place (preserva o tile atual)
  // card SEMANA: consumo <-> mascote. Evento (comemorar/susto) mostra o mascote.
  g_weekFlip = (g_mascEvt && g_weekMasc) ? true : !g_weekFlip;
  week_face_apply();
}

// ---- Animacao dos mascotes (tick unico: um so dono de x/y/escala) ----
static void masc_scale(Mascot &m, float sx, float sy) {
  lv_obj_set_style_transform_scale_x(m.cont, (int32_t)(m.scale * sx), 0);
  lv_obj_set_style_transform_scale_y(m.cont, (int32_t)(m.scale * sy), 0);
}
static void masc_fx_rise(lv_obj_t *o, uint32_t cyc, uint32_t per, int y0, int dy) {
  if (!o) return;
  lv_obj_set_y(o, y0 - (int)(cyc * dy / per));
  lv_obj_set_style_opa(o, (lv_opa_t)(255 - cyc * 255 / per), 0);
}
static void masc_tick(Mascot &m, uint32_t now, int i) {
  if (!m.cont) return;
  float ph = now / 600.0f + i * 0.9f;
  float sx = 1, sy = 1;
  int x = m.baseX, y = m.baseY;
  uint32_t age = now - m.bornMs;

  if (age < 700) {                                   // pulinho ao aparecer
    if (age < 400) {                                 // queda acelerando
      float p = age / 400.0f;
      y -= (int)(90 * (1 - p * p));
    } else if (age < 550) {                          // quique curto
      y -= (int)(10 * sinf((age - 400) / 150.0f * (float)M_PI));
    }
    if (age >= 400 && age < 520) {                   // achata no pouso
      float t = 1 - (age - 400) / 120.0f;
      sx = 1 + 0.12f * t; sy = 1 - 0.15f * t;
    }
  } else if (m.mood == 1) {                          // feliz: balanca + respira
    float w = sinf(ph);
    y += (int)(5 * w);
    sx = 1 + 0.03f * w; sy = 1 - 0.03f * w;
  } else if (m.mood == 2) {                          // suando: balanco curto + tremor
    y += (int)(2 * sinf(ph * 0.6f));
    x += ((now / MASC_TICK_MS) & 1) ? 1 : -1;
  } else if (m.mood == 3) {                          // preocupado: "nega" de lado
    x += (int)(4 * sinf(ph * 0.5f));
  }
  // Reacao em curso sobrepoe o idle (so depois do pulinho de entrada)
  bool heartsOn = false, bangOn = false;
  if (m.react && age >= 700 && (int32_t)(now - m.reactAt) >= 0) {
    uint32_t r = now - m.reactAt;
    if (r >= REACT_MS[m.react]) m.react = REACT_NONE;
    else if (m.react == REACT_HOP) {                 // pulo alto com achatamento no pouso
      y = m.baseY - (int)(30 * sinf(r / 600.0f * (float)M_PI));
      if (r > 480) { float t = (600 - r) / 120.0f; sx = 1 + 0.10f * t; sy = 1 - 0.12f * t; }
    } else if (m.react == REACT_HEARTS) {            // coracoes subindo
      heartsOn = true;
      y = m.baseY - (int)(4 * fabsf(sinf(r / 200.0f)));
    } else if (m.react == REACT_PARTY) {             // 2 pulos + coracoes + balanco
      heartsOn = true;
      y = m.baseY - (int)(22 * fabsf(sinf(r / 500.0f * (float)M_PI)));
      x = m.baseX + (int)(4 * sinf(r / 90.0f));
    } else if (m.react == REACT_SCARED) {            // salto curto, tremedeira e "!"
      bangOn = true;
      y = m.baseY - (r < 250 ? (int)(14 * sinf(r / 250.0f * (float)M_PI)) : 0);
      x = m.baseX + ((r / 40) & 1 ? 3 : -3);
      sx = 0.94f; sy = 1.06f;                        // "encolhe" de medo
    }
  }
  for (int k = 0; k < 3; k++) {
    if (!m.heart[k]) continue;
    if (!heartsOn) { lv_obj_add_flag(m.heart[k], LV_OBJ_FLAG_HIDDEN); continue; }
    lv_obj_clear_flag(m.heart[k], LV_OBJ_FLAG_HIDDEN);
    masc_fx_rise(m.heart[k], (now - m.reactAt + k * 300) % 900, 900, 16, 16);
  }
  if (m.bang) {
    if (bangOn) lv_obj_clear_flag(m.bang, LV_OBJ_FLAG_HIDDEN);
    else lv_obj_add_flag(m.bang, LV_OBJ_FLAG_HIDDEN);
  }
  lv_obj_set_pos(m.cont, x, y);
  masc_scale(m, sx, sy);

  if (m.mood == 1) {
    for (int k = 0; k < 3; k++)                      // brilhos sobem e somem
      masc_fx_rise(m.fx[k], (now + k * 533) % 1600, 1600, 18, 18);
    if (m.pupil[0]) {                                // olhar p/ os lados
      static const int EX[2] = {CLAWD_MD_EYE0_X, CLAWD_MD_EYE1_X};
      if (!m.lookUntil && (int32_t)(now - m.lookAt) > 0) {
        m.lookUntil = now + 1400;
        for (int k = 0; k < 2; k++) {
          lv_obj_clear_flag(m.lid[k], LV_OBJ_FLAG_HIDDEN);
          lv_obj_clear_flag(m.pupil[k], LV_OBJ_FLAG_HIDDEN);
        }
      }
      if (m.lookUntil) {
        if ((int32_t)(now - m.lookUntil) >= 0) {
          for (int k = 0; k < 2; k++) {
            lv_obj_add_flag(m.lid[k], LV_OBJ_FLAG_HIDDEN);
            lv_obj_add_flag(m.pupil[k], LV_OBJ_FLAG_HIDDEN);
          }
          m.lookUntil = 0;
          m.lookAt = now + 4000 + esp_random() % 4000;
        } else {
          uint32_t t = 1400 - (m.lookUntil - now);
          int dx = t < 500 ? -3 : (t < 1000 ? 3 : 0);
          for (int k = 0; k < 2; k++) lv_obj_set_x(m.pupil[k], EX[k] + dx);
        }
      }
    }
  } else if (m.mood == 2) {                          // 2 gotas defasadas
    lv_obj_t *d[2] = {m.drop, m.fx[0]};
    for (int k = 0; k < 2; k++) {
      if (!d[k]) continue;
      uint32_t cyc = (now + k * 450) % 900;
      lv_obj_set_y(d[k], 24 + (int)(cyc * 22 / 900));
      lv_obj_set_style_bg_opa(d[k], (lv_opa_t)(255 - cyc * 190 / 900), 0);
    }
  } else if (m.mood == 3 && m.fx[0]) {               // nuvenzinha flutuando
    lv_obj_set_y(m.fx[0], 2 + (int)(2 * sinf(ph * 1.5f)));
  }
}

// ============================================================
// setup / loop
// ============================================================
void setup() {
  Serial.begin(115200);
  delay(300);
  Serial.println("\n=== Claude Usage Stick (touch) ===");

  // Display
  Arduino_DataBus *bus = new Arduino_ESP32QSPI(TFT_CS, TFT_SCK, TFT_SDA0, TFT_SDA1, TFT_SDA2, TFT_SDA3);
  Arduino_GFX *g = new Arduino_AXS15231B(bus, GFX_NOT_DEFINED, 0, false, 320, 480);
  gfx = new Arduino_Canvas(320, 480, g, 0, 0, 0);
  if (!gfx->begin(QSPI_FREQ)) { Serial.println("FATAL display"); while (1) delay(1000); }
  gfx->fillScreen(0x0000); gfx->flush();
  canvas_fb = gfx->getFramebuffer();

  // Backlight via PWM (brilho ajustável)
  ledcAttach(TFT_BL, 5000, 8);
  touch_dev.begin();

  // LVGL
  lv_init();
  lv_tick_set_cb([]() -> uint32_t { return millis(); });
  uint32_t bufSize = SCREEN_WIDTH * SCREEN_HEIGHT * sizeof(lv_color_t);
  lv_color_t *buf = (lv_color_t *)heap_caps_malloc(bufSize, MALLOC_CAP_SPIRAM | MALLOC_CAP_8BIT);
  if (!buf) { Serial.println("FATAL PSRAM"); fatal_screen("PSRAM indisponivel"); }
  lv_display_t *disp = lv_display_create(SCREEN_WIDTH, SCREEN_HEIGHT);
  lv_display_set_flush_cb(disp, disp_flush_cb);
  // DIRECT (nao FULL): o LVGL redesenha so o que mudou dentro do buffer cheio e
  // entrega o retangulo sujo ao flush_cb. Em FULL, qualquer animacao de 1 pixel
  // custava um render + transposicao de tela inteira.
  lv_display_set_buffers(disp, buf, NULL, bufSize, LV_DISPLAY_RENDER_MODE_DIRECT);
  lv_indev_t *indev = lv_indev_create();
  lv_indev_set_type(indev, LV_INDEV_TYPE_POINTER);
  lv_indev_set_read_cb(indev, touch_read_cb);

  load_persisted();
  apply_brightness();
  boot_splash(TRS("Iniciando...", "Starting..."));

  if (!LittleFS.begin(true)) Serial.println("LittleFS: falhou");
  else {
    // Historico/heatmap sairam na v2.5: libera os arquivos antigos.
    LittleFS.remove("/hist.bin"); LittleFS.remove("/hist0.tmp");
    for (int i = 0; i < ACCT_MAX; i++) {
      char pth[16]; snprintf(pth, sizeof(pth), "/hist%d.bin", i);
      LittleFS.remove(pth);
    }
    load_web_logo();
  }

  g_wifi.begin();

  boot_status(TRS("Conectando ao WiFi...", "Connecting to WiFi..."));
  // Reboot do watchdog de WiFi (loop()): PIN da sessao veio pela RTC RAM.
  // Consumido e zerado aqui; so vale apos reset por software.
  bool rtcOk = esp_reset_reason() == ESP_RST_SW && g_rtc.magic == RTC_PIN_MAGIC &&
               g_hasToken && decryptToken(g_blob, g_rtc.pin, g_token, sizeof(g_token));
  if (rtcOk) strlcpy(g_sessionPin, g_rtc.pin, sizeof(g_sessionPin));
  rtc_session_clear();

  if (rtcOk) {
    Serial.println("[PIN] sessao restaurada apos reboot do watchdog de WiFi");
    g_wifi.autoConnect(WIFI_CONNECT_TIMEOUT_MS, boot_wifi_tick);
    request_state(g_wifi.isConnected() ? ST_LOADING : ST_ERROR);
  } else if (g_hasToken) {
    // Tenta WiFi cedo (em paralelo o usuário digita o PIN)
    g_wifi.autoConnect(WIFI_CONNECT_TIMEOUT_MS, boot_wifi_tick);
    request_state(ST_PIN);
  } else {
    g_onboarding = true;
    // Se já há WiFi salvo (reboot no meio do onboarding), pula direto p/ o token
    request_state(g_wifi.autoConnect(WIFI_CONNECT_TIMEOUT_MS, boot_wifi_tick) ? ST_TOKEN : ST_WIFI);
  }
  g_bootSub = nullptr;                     // render_state() destroi a tela de boot
}

void loop() {
  lv_task_handler();
  // Reconexao nao bloqueante (~15s entre tentativas). Fora da tela de WiFi, que
  // faz scan e connect proprios — um begin() por baixo atrapalharia.
  if (g_state != ST_WIFI) g_wifi.maintain();

  // Servidor web (token no onboarding; /window + /tokens no dashboard)
  if (g_web) {
    g_web->handleClient();
    if (g_state == ST_TOKEN && g_tokenGot) {
      g_tokenGot = false;
      if (g_orEntry) request_state(ST_MAIN);
      else if (g_onboarding || !g_sessionPin[0]) request_state(ST_SETUP_PIN);
      else finalize_pending_token();
    }
  }

  if (g_dirty) {
    g_dirty = false;
    render_state();
    if (g_state == ST_LOADING) {
      lv_task_handler();
      lv_refr_now(NULL);
      do_refresh();
    }
  }

  // Poll automático EM BACKGROUND (sem trocar de tela) + refresh manual
  if (g_state == ST_MAIN && !g_otaBusy && !g_otaRebootAt &&   // sem TLS durante o OTA
      (g_wantRefresh || millis() - g_lastPollMs > (uint32_t)g_pollSec * 1000)) {
    g_wantRefresh = false;
    bg_refresh();           // seta g_lastPollMs no fim
  }

  // ST_ERROR nao tem saida propria: quem cai la (tipico: boot mais rapido que o
  // WiFi) ficava preso na tela de falha ate desligar da tomada. Tenta de novo
  // assim que houver rede.
  if (g_state == ST_ERROR && g_wifi.isConnected() && millis() - g_lastPollMs > 15000) {
    g_lastPollMs = millis();
    request_state(ST_LOADING);
  }

  // Watchdog de WiFi. Log de campo: o AP desassocia (ASSOC_EXPIRE) e depois
  // some do scan (NO_AP_FOUND) por minutos, mesmo com o radio reiniciado pelo
  // maintain(); so reboot recupera. O PIN vai para a RTC RAM e o setup() volta
  // direto ao dashboard. Sem sessao desbloqueada (tela de PIN/onboarding), nao.
  static uint32_t offlineSince = 0;
  if (g_wifi.isConnected() || !g_sessionPin[0] || g_state == ST_WIFI) offlineSince = 0;
  else if (!offlineSince) offlineSince = millis();
  else if (millis() - offlineSince > WIFI_REBOOT_AFTER_MS) reboot_keep_session("WiFi offline");

  if (g_otaRebootAt && (int32_t)(millis() - g_otaRebootAt) >= 0) reboot_keep_session("OTA");

  // Backlight: escurecer quando parado / modo noite (so escreve se mudar)
  static uint32_t lastBl = 0;
  if (millis() - lastBl > 500) { lastBl = millis(); if (backlight_target() != g_blNow) apply_brightness(); }

  // Contagem do bloqueio por PIN errado. 250ms para o segundo virar sem atraso
  // visivel; o tick so reescreve o label quando o valor muda. So ST_PIN: o
  // setup de PIN nao tem tentativa nem bloqueio.
  if (g_state == ST_PIN) {
    static uint32_t lastLock = 0;
    if (millis() - lastLock > 250) { lastLock = millis(); pin_lock_tick(); }
  }

  // Atualização viva: contadores (1s), barra de refresh (250ms), mascotes,
  // slideshow (5s, pausa 10s após qualquer toque)
  if (g_state == ST_MAIN) {
    uint32_t now = millis();
    static uint32_t lastTick = 0, lastBar = 0, lastBob = 0, blinkAt = 0;
    static bool blinkClosed = false;
    if (now - lastTick > 1000) { lastTick = now; dash_tick(); update_tok_row(); }
    if (now - lastBar > 250 && g_ui.refBar) {
      lastBar = now;
      int v;
      if (g_refreshing) v = 1000;
      else {
        uint32_t el = now - g_lastPollMs, per = (uint32_t)g_pollSec * 1000;
        v = el >= per ? 0 : (int)(1000 - (uint64_t)el * 1000 / per);
      }
      lv_bar_set_value(g_ui.refBar, v, LV_ANIM_OFF);
    }
    bool mascOn = g_mascN && g_curTile == 0 && g_ui.wkMasc &&
                  !lv_obj_has_flag(g_ui.wkMasc, LV_OBJ_FLAG_HIDDEN);
    if (mascOn && now - lastBob > MASC_TICK_MS) {   // animação por humor
      lastBob = now;
      for (int i = 0; i < g_mascN; i++) masc_tick(g_masc[i], now, i);
    }
    uint32_t bp = blinkClosed ? 150 : 3000;
    if (now - blinkAt > bp) {                        // piscar (só quem está ok)
      blinkAt = now; blinkClosed = !blinkClosed;
      for (int i = 0; i < g_mascN; i++) {
        if (g_masc[i].mood != 1 || g_masc[i].lookUntil) continue;   // olhando: palpebra e do olhar
        for (int k = 0; k < 2; k++) {
          if (!g_masc[i].lid[k]) continue;
          if (blinkClosed) lv_obj_clear_flag(g_masc[i].lid[k], LV_OBJ_FLAG_HIDDEN);
          else             lv_obj_add_flag(g_masc[i].lid[k], LV_OBJ_FLAG_HIDDEN);
        }
      }
    }
    if (g_slideSec > 0 && g_ui.tv && !g_refreshing && !g_mo.scrim &&
        now - g_lastTouchMs > 10000 && now - g_lastSlideMs > (uint32_t)g_slideSec * 1000) {
      g_lastSlideMs = now;
      int next = (g_curTile + 1) % (g_hasOr ? 2 : 1);
      lv_tileview_set_tile_by_index(g_ui.tv, next, 0, LV_ANIM_ON);
    }

    // Momentos de limiar: mostra pendente e anima o overlay ativo
    if (g_pendWin >= 0 && !g_mo.scrim && !g_refreshing) {
      show_moment(g_pendWin, g_pendThr);
      g_pendWin = -1;
    }
    if (g_mo.scrim) moment_tick();
  }

  delay(5);
}
