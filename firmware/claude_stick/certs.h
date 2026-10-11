#pragma once

// Root CA bundle para os endpoints HTTPS (api.anthropic.com, status.claude.com, openrouter.ai).
// Múltiplas raízes para sobreviver a rotação de CA do servidor:
//   GlobalSign Root CA      — âncora atual da api.anthropic.com (expira 2028-01-28)
//   ISRG Root X1            — Let's Encrypt, âncora atual da status.claude.com (expira 2035-06-04)
//   DigiCert Global Root G2 — alvo comum de rotação (expira 2038-01-15)
//   GTS Root R4             — Google Trust Services, âncora da openrouter.ai (expira 2036-06-22)
extern const char CA_BUNDLE[];
