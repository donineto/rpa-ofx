from pathlib import Path
import io
import time
import shutil
import logging
from datetime import datetime
import re
import unicodedata
from xml.sax.saxutils import escape

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import pandas as pd
from ofxparse import OfxParser
from watchdog.observers import Observer
from watchdog.events import FileSystemEventHandler
import threading
import os
import smtplib
from email.message import EmailMessage
from dotenv import load_dotenv

# ------------------------------------------------------------------
# CONTROLE DE DUPLICIDADE
# ------------------------------------------------------------------
_processing_lock = threading.Lock()
_files_in_process: set = set()

from reportlab.lib import colors
from reportlab.lib.enums import TA_LEFT, TA_CENTER, TA_RIGHT
from reportlab.lib.pagesizes import A4, landscape
from reportlab.lib.styles import getSampleStyleSheet, ParagraphStyle
from reportlab.lib.units import cm
from reportlab.platypus import (
    SimpleDocTemplate,
    Paragraph,
    Spacer,
    Table,
    TableStyle,
    PageBreak,
    Image,
    HRFlowable,
)


# ---------------------------------------------------------------------------
# DIRETÓRIOS
# ---------------------------------------------------------------------------

BASE_DIR      = Path(__file__).resolve().parent
load_dotenv(dotenv_path=BASE_DIR / ".env")

INPUT_DIR     = BASE_DIR / "entrada"
OUTPUT_DIR    = BASE_DIR / "saida"
PROCESSED_DIR = BASE_DIR / "processados"
ERROR_DIR     = BASE_DIR / "erros"
EMAIL_ERROR_DIR = BASE_DIR / "erros_email"
LOG_DIR       = BASE_DIR / "logs"

POLL_INTERVAL_SECONDS = 5

# ---------------------------------------------------------------------------
# CATEGORIAS
# ---------------------------------------------------------------------------

CATEGORY_TRANSFER_INTERNAL    = "Transferência entre contas próprias"
CATEGORY_FIXED_EXPENSE        = "Despesas fixas"
CATEGORY_VARIABLE_EXPENSE     = "Despesas variáveis"
CATEGORY_THIRD_PARTY_SERVICE  = "Serviços de terceiros / honorários"
CATEGORY_FUEL_LOGISTICS       = "Combustível / deslocamento"
CATEGORY_SOFTWARE_SYSTEMS     = "Software / sistemas"
CATEGORY_BANK_TARIFF          = "Tarifas bancárias"
CATEGORY_SUPPLIER_PAYMENT     = "Pagamento a fornecedor"
CATEGORY_UNCLASSIFIED_EXPENSE = "Gastos não classificados"
CATEGORY_UNCLASSIFIED_INCOME  = "Entradas não classificadas"
CATEGORY_NEUTRAL              = "Neutra / Não classificada"

TRANSFER_CATEGORIES = {CATEGORY_TRANSFER_INTERNAL}
UNCLASSIFIED_CATEGORIES = {
    CATEGORY_UNCLASSIFIED_INCOME,
    CATEGORY_UNCLASSIFIED_EXPENSE,
    CATEGORY_NEUTRAL,
}

# ---------------------------------------------------------------------------
# BANCOS
# ---------------------------------------------------------------------------

BANK_CODE_MAP = {
    "001": "Banco do Brasil",         "033": "Santander",
    "041": "Banrisul",                "077": "Banco Inter",
    "104": "Caixa Econômica Federal", "212": "Banco Original",
    "237": "Bradesco",                "260": "Nubank",
    "290": "PagBank",                 "323": "Mercado Pago",
    "336": "C6 Bank",                 "341": "Itaú",
    "422": "Banco Safra",             "748": "Sicredi",
    "756": "Sicoob",
}

BANK_NAME_HINTS = {
    "ITAU": "Itaú",                "BRADESCO": "Bradesco",
    "SANTANDER": "Santander",      "BANCO DO BRASIL": "Banco do Brasil",
    " BB ": "Banco do Brasil",     "CAIXA": "Caixa Econômica Federal",
    "NUBANK": "Nubank",            "INTER": "Banco Inter",
    "SICREDI": "Sicredi",          "SICOOB": "Sicoob",
    "C6": "C6 Bank",               "ORIGINAL": "Banco Original",
    "PAGBANK": "PagBank",          "MERCADO PAGO": "Mercado Pago",
    "SAFRA": "Banco Safra",
}

# ---------------------------------------------------------------------------
# KEYWORDS DE CLASSIFICAÇÃO
# ---------------------------------------------------------------------------

ESTORNO_KEYWORDS = [
    "ESTORNO", "REVERSAO", "REVERSAO PIX", "DEVOLUCAO",
    "DEVOLUCAO PIX", "CHARGEBACK", "CANCELAMENTO",
]

TRANSFER_INTERNAL_KEYWORDS = [
    "MESMA TITULARIDADE", "ENTRE CONTAS", "TRANSFERENCIA ENTRE CONTAS",
    "TRANSF ENTRE CONTAS", "PIX ENTRE CONTAS", "PIX MESMA TITULARIDADE",
    "TED MESMA TITULARIDADE", "TRANSF P/ MESMA TITULARIDADE",
    "TRANSF MESMA TITULARIDADE", "TRF ENTRE CONTAS",
]

TARIFF_KEYWORDS = [
    "TARIFA", "CESTA", "PACOTE", "ANUIDADE",
    "SERVICO BANCARIO", "SERV BANC",
    "TAR PACOTE", "TAR TED", "TAR PIX",
    "EXTRATO MENSAL", "AVISO SMS",
    "TARIFA MANUTENCAO CONTA", "MANUTENCAO CONTA PJ",
    "TARIFA COBRANCA", "TARIFA BANCARIA"
]

INTEREST_KEYWORDS = [
    "JUROS", "MULTA", "ENCARGOS", "MORA", "IOF"
]

TAX_KEYWORDS = [
    "DARF", "DAS", "GPS", "FGTS", "INSS", "IRRF", "IRPJ", "ISS",
    "ICMS", "PIS", "COFINS", "CSLL", "TRIBUTO", "IMPOSTO", "IPTU", "IPVA"
]

PAYROLL_KEYWORDS = [
    "SALARIO", "PRO LABORE", "PRO-LABORE", "FOLHA",
    "PAGAMENTO SALARIO", "CRED SALARIO", "PAGTO FUNCIONARIO",
    "ADIANTAMENTO SALARIAL", "HOLERITE"
]

SUPPLIER_KEYWORDS = [
    "FORNECEDOR", "PAGAMENTO FORNECEDOR", "NOTA FISCAL", "NFS-E",
    "NFSE", "BOLETO FORNECEDOR", "PAGTO FORN", "PAGAMENTO NF",
    "FATURA FORNECEDOR"
]

FIXED_EXPENSE_KEYWORDS = [
    "DEB AUT", "DEBITO AUTOMATICO", "DEB.AUT", "ENERGIA", "LUZ", "AGUA",
    "SANEAMENTO", "TELEFONE", "CELULAR", "INTERNET", "ALUGUEL",
    "SEGURO", "CONDOMINIO", "ESCOLA", "PLANO DE SAUDE",
    "ASSINATURA"
]

SOFTWARE_SYSTEMS_KEYWORDS = [
    "SOFTWARE", "SISTEMA", "LICENCA", "LICENÇA", "ASSINATURA",
    "PLATAFORMA", "ERP", "CRM", "HOSPEDAGEM", "DOMINIO", "DOMÍNIO",
    "SERVIDOR", "NUVEM", "CLOUD", "MANUTENCAO SOFTWARE", "MANUTENÇÃO SOFTWARE"
]

THIRD_PARTY_SERVICE_KEYWORDS = [
    "HONORARIO", "HONORARIOS", "HONORÁRIO", "HONORÁRIOS",
    "TERCEIROS", "PRESTADOR", "CONSULTORIA", "ASSESSORIA",
    "SERVICO TERCEIRIZADO", "SERVIÇO TERCEIRIZADO",
    "SERVICOS TERCEIRIZADOS", "SERVIÇOS TERCEIRIZADOS",
    "FREELANCER"
]

FUEL_LOGISTICS_KEYWORDS = [
    "POSTO", "COMBUSTIVEL", "COMBUSTÍVEL", "GASOLINA", "ETANOL", "DIESEL",
    "UBER", "99APP", "PEDAGIO", "PEDÁGIO", "ESTACIONAMENTO", "FRETE"
]

VARIABLE_EXPENSE_KEYWORDS = [
    "COMPRA", "PURCHASE", "CARTAO", "CARTÃO", "CART", "DEBITO", "DÉBITO",
    "POS", "ELO", "VISA", "MASTERCARD", "AMEX", "HIPERCARD",
    "ESTAB", "LOJA", "QR CODE", "PAGTO ELETRON",
    "COMPRA DEBITO", "COMPRA DÉBITO", "COMPRA CARTAO", "COMPRA CARTÃO",
    "MERCADO", "SUPERMERCADO", "RESTAURANTE", "LANCHONETE",
    "PAPELARIA", "MATERIAL ESCRITORIO", "MATERIAL ESCRITÓRIO",
    "LIMPEZA", "INSUMO", "MATERIAL", "PECA", "PEÇA"
]

BOLETO_KEYWORDS = [
    "BOLETO", "PAGTO BOLETO", "PAGAMENTO BOLETO", "PAGTO TITULO",
    "PAGAMENTO TITULO", "TITULO", "TÍTULO", "COBRANCA BANCARIA"
]

INVESTMENT_KEYWORDS = [
    "APLICACAO", "APLICAÇÃO", "INVESTIMENTO", "CDB", "FUNDO", "POUPANCA",
    "POUPANÇA", "RESGATE AUTOMATICO", "RESGATE AUTOMÁTICO",
    "APLIC AUTO", "RESG AUTOM", "RENDIMENTO APLICACAO", "RENDIMENTO APLICAÇÃO"
]

LOAN_KEYWORDS = [
    "EMPRESTIMO", "EMPRÉSTIMO", "FINANCIAMENTO", "CREDITO CONTRATADO",
    "CRÉDITO CONTRATADO", "PARCELA EMPRESTIMO", "PARCELA EMPRÉSTIMO",
    "CAPITAL DE GIRO"
]

OPERATIONAL_REVENUE_KEYWORDS = [
    "VENDA", "CLIENTE", "COBRANCA", "FATURA RECEBIDA", "CREDITO CLIENTE",
    "CRÉDITO CLIENTE", "DUPLICATA", "LIQUIDACAO", "LIQUIDAÇÃO",
    "RECEBIMENTO CLIENTE", "RECEITA OPERACIONAL", "BOLETO LIQUIDADO",
    "COBRANCA LIQUIDADA"
]

GENERIC_EXPENSE_CHANNEL_KEYWORDS = [
    "PIX", "TED", "DOC", "TRANSFERENCIA", "TRANSFERÊNCIA", "TRANSF", "TRANSFER",
    "PAGAMENTO PIX", "TED ENVIADA", "DOC ENVIADO", "TRANSF ELET DISP"
]

GENERIC_INCOME_CHANNEL_KEYWORDS = [
    "PIX", "TED", "DOC", "TRANSFERENCIA", "TRANSFERÊNCIA", "TRANSF", "TRANSFER",
    "DEPOSITO", "DEPÓSITO", "CREDITO", "CRÉDITO", "RECEBIMENTO",
    "RECEBIDO", "CREDITO CONTA", "CRÉDITO CONTA",
    "DEP DINH", "TED RECEBIDA", "PIX RECEBIDO"
]

# ---------------------------------------------------------------------------
# SUBTÍTULOS DOS CARDS
# ---------------------------------------------------------------------------

CARD_SUBTITLES = {
    "total_entradas":            "Total recebido no período",
    "total_saidas":              "Total pago no período",
    "saldo_periodo":             "Diferença entre entradas e saídas",
    "indice_cobertura":          "Entradas ÷ Saídas",
    "dias_pressao_caixa":        "Dias com saldo negativo",
    "ticket_medio_entrada":      "Valor médio por recebimento",
    "ticket_medio_saida":        "Valor médio por pagamento",
    "percentual_transferencias": "Transferências internas s/ total",
    "dia_maior_recebimento":     "Pico de recebimento no período",
    "dia_maior_pagamento":       "Pico de pagamento no período",
}

# ---------------------------------------------------------------------------
# SETUP
# ---------------------------------------------------------------------------

def setup_folders():
    for folder in [INPUT_DIR, OUTPUT_DIR, PROCESSED_DIR, ERROR_DIR, EMAIL_ERROR_DIR, LOG_DIR]:
        folder.mkdir(parents=True, exist_ok=True)


def setup_logging():
    log_file = LOG_DIR / "rpa.log"
    logging.basicConfig(
        level=logging.INFO,
        format="%(asctime)s | %(levelname)s | %(message)s",
        handlers=[
            logging.FileHandler(log_file, encoding="utf-8"),
            logging.StreamHandler(),
        ],
    )

# ---------------------------------------------------------------------------
# UTILITÁRIOS DE ARQUIVO
# ---------------------------------------------------------------------------

def wait_until_file_is_ready(file_path: Path, timeout=30) -> bool:
    start     = time.time()
    last_size = -1
    while time.time() - start < timeout:
        if not file_path.exists():
            time.sleep(1)
            continue
        current_size = file_path.stat().st_size
        if current_size > 0 and current_size == last_size:
            return True
        last_size = current_size
        time.sleep(1)
    return False


def move_with_unique_name(src: Path, dst_folder: Path) -> Path:
    destination = dst_folder / src.name
    if not destination.exists():
        shutil.move(str(src), str(destination))
        return destination
    timestamp   = datetime.now().strftime("%Y%m%d_%H%M%S")
    destination = dst_folder / f"{src.stem}_{timestamp}{src.suffix}"
    shutil.move(str(src), str(destination))
    return destination

# ---------------------------------------------------------------------------
# UTILITÁRIOS DE TEXTO
# ---------------------------------------------------------------------------

def normalize_text(text: str) -> str:
    text = text or ""
    text = unicodedata.normalize("NFKD", text)
    text = "".join(c for c in text if not unicodedata.combining(c))
    text = text.upper()
    text = re.sub(r"\s+", " ", text).strip()
    return text


def sanitize_for_pdf(text: str) -> str:
    text = text or ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f\x7f]", " ", text)
    text = text.replace("\n", " ").replace("\r", " ").replace("\t", " ")
    text = re.sub(r"\s+", " ", text).strip()
    return escape(text)


def has_any(text: str, keywords: list) -> bool:
    return any(keyword in text for keyword in keywords)


def format_currency(value: float) -> str:
    return f"R$ {value:,.2f}".replace(",", "X").replace(".", ",").replace("X", ".")


def format_number(value: float) -> str:
    return f"{value:,.2f}".replace(",", "X").replace(".", ",").replace("X", ".")


def format_percent(value: float) -> str:
    return f"{value:.2f}%".replace(".", ",")

# ---------------------------------------------------------------------------
# BANCO
# ---------------------------------------------------------------------------

def infer_bank_name(file_path: Path, bank_id: str) -> str:
    raw_bank = re.sub(r"\D", "", str(bank_id or ""))
    if len(raw_bank) >= 3:
        bank_code = raw_bank[:3]
        if bank_code in BANK_CODE_MAP:
            return BANK_CODE_MAP[bank_code]
    normalized_stem = f" {normalize_text(file_path.stem)} "
    for hint, bank_name in BANK_NAME_HINTS.items():
        if hint in normalized_stem:
            return bank_name
    return "Banco não identificado"

# ---------------------------------------------------------------------------
# CLASSIFICAÇÃO
# ---------------------------------------------------------------------------

def classify_transaction(description: str, amount: float) -> str:
    desc = normalize_text(description)

    # 1. Regras especiais
    if has_any(desc, ESTORNO_KEYWORDS):
        return "Estorno / Devolução"

    if has_any(desc, TRANSFER_INTERNAL_KEYWORDS):
        return CATEGORY_TRANSFER_INTERNAL

    # 2. Saídas específicas
    if amount < 0 and has_any(desc, TAX_KEYWORDS):
        return "Impostos / Tributos"

    if amount < 0 and has_any(desc, INTEREST_KEYWORDS):
        return "Juros / Encargos"

    if has_any(desc, PAYROLL_KEYWORDS):
        return "Folha / Pró-labore"

    if amount < 0 and has_any(desc, SUPPLIER_KEYWORDS):
        return CATEGORY_SUPPLIER_PAYMENT

    if amount < 0 and has_any(desc, THIRD_PARTY_SERVICE_KEYWORDS):
        return CATEGORY_THIRD_PARTY_SERVICE

    if amount < 0 and has_any(desc, FUEL_LOGISTICS_KEYWORDS):
        return CATEGORY_FUEL_LOGISTICS

    if amount < 0 and has_any(desc, SOFTWARE_SYSTEMS_KEYWORDS):
        return CATEGORY_SOFTWARE_SYSTEMS

    if amount < 0 and has_any(desc, FIXED_EXPENSE_KEYWORDS):
        return CATEGORY_FIXED_EXPENSE

    if amount < 0 and has_any(desc, TARIFF_KEYWORDS):
        return CATEGORY_BANK_TARIFF

    if has_any(desc, BOLETO_KEYWORDS):
        return "Boletos / Títulos"

    if has_any(desc, INVESTMENT_KEYWORDS):
        return "Investimentos / Aplicações" if amount < 0 else "Resgates / Aplicações"

    if has_any(desc, LOAN_KEYWORDS):
        return "Empréstimos / Financiamentos"

    # 3. Entradas operacionais
    if amount > 0 and has_any(desc, OPERATIONAL_REVENUE_KEYWORDS):
        return "Receita operacional"

    # 4. Despesas variáveis
    if amount < 0 and has_any(desc, VARIABLE_EXPENSE_KEYWORDS):
        return CATEGORY_VARIABLE_EXPENSE

    # 5. Canais genéricos - só depois das regras específicas
    if amount < 0 and has_any(desc, GENERIC_EXPENSE_CHANNEL_KEYWORDS):
        return CATEGORY_UNCLASSIFIED_EXPENSE

    if amount > 0 and has_any(desc, GENERIC_INCOME_CHANNEL_KEYWORDS):
        return CATEGORY_UNCLASSIFIED_INCOME

    # 6. Fallback final
    if amount > 0:
        return CATEGORY_UNCLASSIFIED_INCOME

    if amount < 0:
        return CATEGORY_UNCLASSIFIED_EXPENSE

    return CATEGORY_NEUTRAL

# ---------------------------------------------------------------------------
# PARSE OFX
# ---------------------------------------------------------------------------

def parse_ofx(file_path: Path):
    with open(file_path, "rb") as f:
        ofx = OfxParser.parse(f)

    account      = getattr(ofx, "account", None)
    statement    = getattr(account, "statement", None)
    bank_id      = getattr(account, "routing_number", "") if account else ""
    start_date   = getattr(statement, "start_date", None) if statement else None
    end_date     = getattr(statement, "end_date",   None) if statement else None
    transactions = getattr(statement, "transactions", []) if statement else []

    rows, inconsistencies = [], []

    for tx in transactions:
        amount      = float(tx.amount) if tx.amount is not None else 0.0
        date_value  = tx.date.strftime("%Y-%m-%d %H:%M:%S") if tx.date else ""
        memo        = (tx.memo  or "").strip()
        payee       = (tx.payee or "").strip()
        description = " | ".join([p for p in [payee, memo] if p]).strip()

        if not description:
            description = "SEM_DESCRICAO"
            inconsistencies.append("Transação com descrição vazia.")

        tx_type  = "Entrada" if amount > 0 else "Saída" if amount < 0 else "Neutra"
        category = classify_transaction(description, amount)

        rows.append({
            "data":       date_value,
            "descricao":  description,
            "valor":      amount,
            "tipo":       tx_type,
            "categoria":  category,
            "cheque":     getattr(tx, "checknum", ""),
            "referencia": getattr(tx, "id", ""),
        })

    df        = pd.DataFrame(rows)
    bank_name = infer_bank_name(file_path, bank_id)

    metadata = {
        "arquivo":               file_path.name,
        "banco":                 bank_name,
        "banco_codigo":          str(bank_id or ""),
        "inicio_extrato":        start_date.strftime("%Y-%m-%d %H:%M:%S") if start_date else "",
        "fim_extrato":           end_date.strftime("%Y-%m-%d %H:%M:%S")   if end_date   else "",
        "quantidade_transacoes": len(df),
    }
    return df, metadata, inconsistencies

def validate_parsed_ofx(df: pd.DataFrame, metadata: dict, inconsistencies: list):
    fatal_errors = []

    if df is None or df.empty:
        fatal_errors.append("Arquivo OFX sem transações válidas.")

    if not metadata.get("inicio_extrato") and not metadata.get("fim_extrato"):
        fatal_errors.append("OFX sem período de extrato identificado.")

    if not metadata.get("banco_codigo"):
        inconsistencies.append("Código do banco não identificado no OFX.")

    if not df.empty:
        if "data" not in df.columns or df["data"].isna().all():
            fatal_errors.append("Nenhuma data de transação foi lida.")

        datas_convertidas = pd.to_datetime(df["data"], errors="coerce")
        if datas_convertidas.isna().all():
            fatal_errors.append("Todas as datas das transações são inválidas.")

        if "valor" not in df.columns:
            fatal_errors.append("Campo de valor ausente nas transações.")
        else:
            valores = pd.to_numeric(df["valor"], errors="coerce")
            if valores.isna().all():
                fatal_errors.append("Nenhum valor numérico válido foi lido.")

        if "referencia" in df.columns:
            refs = (
                df["referencia"]
                .fillna("")
                .astype(str)
                .str.strip()
            )
            refs_validas = refs[refs != ""]
            if not refs_validas.empty and refs_validas.duplicated().any():
                fatal_errors.append("OFX com referências/FITID duplicados.")

    return fatal_errors, inconsistencies

# ---------------------------------------------------------------------------
# PREPARAÇÃO DE DADOS
# ---------------------------------------------------------------------------

def prepare_dataframe(df: pd.DataFrame) -> pd.DataFrame:
    if df.empty:
        return df.copy()
    work_df = df.copy()
    work_df["data"] = pd.to_datetime(work_df["data"], errors="coerce")
    work_df = work_df.dropna(subset=["data"]).copy()
    work_df["dia"]            = work_df["data"].dt.date
    work_df["valor_absoluto"] = work_df["valor"].abs()
    return work_df


def build_daily_summary(df: pd.DataFrame) -> pd.DataFrame:
    work_df = prepare_dataframe(df)
    if work_df.empty:
        return pd.DataFrame(columns=[
            "dia", "entradas", "saidas", "fluxo_liquido",
            "saldo_acumulado", "quantidade_transacoes",
        ])
    rows = []
    for dia, group in work_df.groupby("dia"):
        rows.append({
            "dia":                   dia,
            "entradas":              float(group.loc[group["valor"] > 0, "valor"].sum()),
            "saidas":                float(abs(group.loc[group["valor"] < 0, "valor"].sum())),
            "fluxo_liquido":         float(group["valor"].sum()),
            "quantidade_transacoes": int(len(group)),
        })
    result = pd.DataFrame(rows).sort_values("dia").reset_index(drop=True)
    result["saldo_acumulado"] = result["fluxo_liquido"].cumsum()
    return result


def build_category_summary(df: pd.DataFrame) -> pd.DataFrame:
    """Retorna resumo de DESPESAS por categoria (exceto transferências internas)."""
    work_df = prepare_dataframe(df)
    if work_df.empty:
        return pd.DataFrame(columns=[
            "categoria", "valor_total", "quantidade_transacoes", "participacao_percentual",
        ])
    saidas_df = work_df[
        (work_df["valor"] < 0) & (~work_df["categoria"].isin(TRANSFER_CATEGORIES))
    ].copy()
    if saidas_df.empty:
        return pd.DataFrame(columns=[
            "categoria", "valor_total", "quantidade_transacoes", "participacao_percentual",
        ])
    category_df = (
        saidas_df.groupby("categoria")
        .agg(valor_total=("valor_absoluto", "sum"), quantidade_transacoes=("categoria", "size"))
        .reset_index()
        .sort_values("valor_total", ascending=False)
    )
    total = category_df["valor_total"].sum()
    category_df["participacao_percentual"] = (
        category_df["valor_total"] / total * 100 if total else 0
    )
    return category_df


def build_income_category_summary(df: pd.DataFrame) -> pd.DataFrame:
    """Retorna resumo de ENTRADAS por categoria (exceto transferências internas)."""
    work_df = prepare_dataframe(df)
    if work_df.empty:
        return pd.DataFrame(columns=[
            "categoria", "valor_total", "quantidade_transacoes", "participacao_percentual",
        ])
    entradas_df = work_df[
        (work_df["valor"] > 0) & (~work_df["categoria"].isin(TRANSFER_CATEGORIES))
    ].copy()
    if entradas_df.empty:
        return pd.DataFrame(columns=[
            "categoria", "valor_total", "quantidade_transacoes", "participacao_percentual",
        ])
    category_df = (
        entradas_df.groupby("categoria")
        .agg(valor_total=("valor_absoluto", "sum"), quantidade_transacoes=("categoria", "size"))
        .reset_index()
        .sort_values("valor_total", ascending=False)
    )
    total = category_df["valor_total"].sum()
    category_df["participacao_percentual"] = (
        category_df["valor_total"] / total * 100 if total else 0
    )
    return category_df


def build_top_movements(df: pd.DataFrame):
    work_df = prepare_dataframe(df)
    if work_df.empty:
        return pd.DataFrame(), pd.DataFrame()
    maiores_entradas = (
        work_df[work_df["valor"] > 0].sort_values("valor", ascending=False).head(5).copy()
    )
    maiores_saidas = (
        work_df[work_df["valor"] < 0].sort_values("valor", ascending=True).head(5).copy()
    )
    return maiores_entradas, maiores_saidas


def build_indicator_dict(df: pd.DataFrame) -> dict:
    work_df = prepare_dataframe(df)
    if work_df.empty:
        return {
            "quantidade_transacoes": 0, "total_entradas": 0.0, "total_saidas": 0.0,
            "saldo_periodo": 0.0, "ticket_medio_entrada": 0.0, "ticket_medio_saida": 0.0,
            "indice_cobertura": 0.0, "dias_pressao_caixa": 0,
            "percentual_transferencias": 0.0,
            "dia_maior_recebimento": "-", "valor_maior_recebimento": 0.0,
            "dia_maior_pagamento":   "-", "valor_maior_pagamento":   0.0,
        }

    entradas = work_df[work_df["valor"] > 0]["valor"]
    saidas   = work_df[work_df["valor"] < 0]["valor"]

    total_entradas       = float(entradas.sum())
    total_saidas         = float(abs(saidas.sum()))
    saldo_periodo        = float(work_df["valor"].sum())
    ticket_medio_entrada = float(entradas.mean()) if not entradas.empty else 0.0
    ticket_medio_saida   = float(abs(saidas.mean())) if not saidas.empty else 0.0
    indice_cobertura     = float(total_entradas / total_saidas) if total_saidas else 0.0

    daily_df           = build_daily_summary(work_df)
    dias_pressao_caixa = int((daily_df["fluxo_liquido"] < 0).sum()) if not daily_df.empty else 0

    if not daily_df.empty:
        max_rec = daily_df.loc[daily_df["entradas"].idxmax()]
        max_pag = daily_df.loc[daily_df["saidas"].idxmax()]
        dia_maior_recebimento   = max_rec["dia"].strftime("%d/%m/%Y")
        valor_maior_recebimento = float(max_rec["entradas"])
        dia_maior_pagamento     = max_pag["dia"].strftime("%d/%m/%Y")
        valor_maior_pagamento   = float(max_pag["saidas"])
    else:
        dia_maior_recebimento = dia_maior_pagamento = "-"
        valor_maior_recebimento = valor_maior_pagamento = 0.0

    movimentacao_total        = total_entradas + total_saidas
    transfer_total            = float(
        work_df[work_df["categoria"].isin(TRANSFER_CATEGORIES)]["valor_absoluto"].sum()
    )
    percentual_transferencias = (
        float(transfer_total / movimentacao_total * 100) if movimentacao_total else 0.0
    )

    return {
        "quantidade_transacoes":     int(len(work_df)),
        "total_entradas":            total_entradas,
        "total_saidas":              total_saidas,
        "saldo_periodo":             saldo_periodo,
        "ticket_medio_entrada":      ticket_medio_entrada,
        "ticket_medio_saida":        ticket_medio_saida,
        "indice_cobertura":          indice_cobertura,
        "dias_pressao_caixa":        dias_pressao_caixa,
        "percentual_transferencias": percentual_transferencias,
        "dia_maior_recebimento":     dia_maior_recebimento,
        "valor_maior_recebimento":   valor_maior_recebimento,
        "dia_maior_pagamento":       dia_maior_pagamento,
        "valor_maior_pagamento":     valor_maior_pagamento,
    }


def build_indicators(df: pd.DataFrame) -> pd.DataFrame:
    m = build_indicator_dict(df)
    return pd.DataFrame([{"indicador": k, "valor": v} for k, v in m.items()])

# ---------------------------------------------------------------------------
# GRÁFICOS
# ---------------------------------------------------------------------------

CHART_GREEN  = "#00B050"
CHART_RED    = "#C00000"
CHART_BLUE   = "#1F77B4"
CHART_ORANGE = "#FF7F0E"
CHART_PURPLE = "#9467BD"
CHART_TEAL   = "#2CA02C"
CHART_PINK   = "#D62728"

PIE_COLORS = [CHART_BLUE, CHART_ORANGE, CHART_TEAL, CHART_PINK, CHART_PURPLE]
BAR_COLORS = ["#1D4ED8", "#2563EB", "#3B82F6", "#60A5FA", "#93C5FD"]


def _annotate_bars(ax, rects, fmt="{:.0f}", fontsize=7):
    for rect in rects:
        height = rect.get_height()
        if height > 0:
            ax.annotate(
                fmt.format(height),
                xy=(rect.get_x() + rect.get_width() / 2, height),
                xytext=(0, 3), textcoords="offset points",
                ha="center", va="bottom", fontsize=fontsize,
            )


def draw_chart_daily(daily_df: pd.DataFrame) -> io.BytesIO:
    """Barras Entradas × Saídas + linha Saldo Acumulado no eixo secundário."""
    buffer = io.BytesIO()
    fig, ax1 = plt.subplots(figsize=(15, 5.5))
    fig.patch.set_facecolor("white")

    if daily_df.empty:
        ax1.text(0.5, 0.5, "Sem dados para o gráfico diário", ha="center", va="center")
        ax1.axis("off")
    else:
        x       = list(range(len(daily_df)))
        width   = 0.36
        x_left  = [i - width / 2 for i in x]
        x_right = [i + width / 2 for i in x]
        labels  = [pd.to_datetime(str(d)).strftime("%d/%m") for d in daily_df["dia"]]

        bars_in  = ax1.bar(x_left,  daily_df["entradas"], width=width,
                           label="Entradas", color=CHART_GREEN, zorder=3)
        bars_out = ax1.bar(x_right, daily_df["saidas"],   width=width,
                           label="Saídas",   color=CHART_RED,   zorder=3)

        _annotate_bars(ax1, bars_in,  fontsize=6)
        _annotate_bars(ax1, bars_out, fontsize=6)

        ax1.set_ylabel("Valor (R$)", fontsize=10, color="#334155")
        ax1.set_xticks(x)
        ax1.set_xticklabels(labels, rotation=45, ha="right", fontsize=8)
        ax1.grid(axis="y", linestyle="--", alpha=0.2, zorder=0)
        ax1.spines["top"].set_visible(False)

        ax2        = ax1.twinx()
        saldo_vals = daily_df["saldo_acumulado"].tolist()
        ax2.plot(x, saldo_vals, color="#7C3AED", linewidth=2.2, marker="o",
                 markersize=4.5, label="Saldo Acumulado", zorder=4)
        ax2.fill_between(x, saldo_vals, alpha=0.08, color="#7C3AED", zorder=2)
        ax2.set_ylabel("Saldo Acumulado (R$)", fontsize=10, color="#7C3AED")
        ax2.tick_params(axis="y", labelcolor="#7C3AED", labelsize=8)
        ax2.spines["top"].set_visible(False)

        handles1, labels1 = ax1.get_legend_handles_labels()
        handles2, labels2 = ax2.get_legend_handles_labels()
        ax1.legend(handles1 + handles2, labels1 + labels2,
                   frameon=False, fontsize=9, loc="upper left")
        ax1.set_title("Entradas × Saídas por Dia  |  Saldo Acumulado",
                      fontsize=12, fontweight="bold", pad=12)

    fig.tight_layout()
    fig.savefig(buffer, format="png", dpi=180, bbox_inches="tight")
    plt.close(fig)
    buffer.seek(0)
    return buffer


def draw_chart_categories_pie(category_df: pd.DataFrame) -> io.BytesIO:
    """
    Gráfico de pizza — proporcional, sem distorção.
    Tamanho da figura quadrado garante que o círculo não fique oval.
    """
    buffer  = io.BytesIO()
    # ── figura quadrada: mesma dimensão nos 2 eixos ──
    fig, ax = plt.subplots(figsize=(6.5, 6.5))
    fig.patch.set_facecolor("white")

    plot_df = category_df.head(5).copy()
    if plot_df.empty:
        ax.text(0.5, 0.5, "Sem dados de categorias", ha="center", va="center")
        ax.axis("off")
    else:
        wedges, texts, autotexts = ax.pie(
            plot_df["valor_total"],
            labels=None,
            autopct="%1.1f%%",
            startangle=90,
            colors=PIE_COLORS[: len(plot_df)],
            pctdistance=0.78,
            wedgeprops={"linewidth": 1, "edgecolor": "white"},
        )
        for at in autotexts:
            at.set_fontsize(9)
        ax.legend(
            wedges, plot_df["categoria"],
            loc="lower center", bbox_to_anchor=(0.5, -0.14),
            ncol=2, fontsize=8, frameon=False,
        )
        ax.set_title("Top 5 Categorias de Despesa", fontsize=12, fontweight="bold")
        ax.axis("equal")   # garante círculo perfeito

    fig.tight_layout()
    fig.savefig(buffer, format="png", dpi=180, bbox_inches="tight")
    plt.close(fig)
    buffer.seek(0)
    return buffer


def draw_chart_categories_bar(category_df: pd.DataFrame) -> io.BytesIO:
    """
    Gráfico de barras horizontais — proporcional, sem distorção.
    Altura calculada dinamicamente pelo número de categorias.
    """
    buffer  = io.BytesIO()
    plot_df = category_df.head(5).copy().sort_values("valor_total", ascending=True)

    n_bars      = max(len(plot_df), 1)
    # ── altura dinâmica: ~1.1 por barra + margens, mínimo 4.5, máximo 6.5 ──
    fig_height  = 5.5
    fig_width   = 8.5   # largura fixa moderada — não esticar só na horizontal

    fig, ax = plt.subplots(figsize=(fig_width, fig_height))
    fig.patch.set_facecolor("white")

    if plot_df.empty:
        ax.text(0.5, 0.5, "Sem dados de categorias", ha="center", va="center")
        ax.axis("off")
    else:
        y_pos = list(range(len(plot_df)))
        bars  = ax.barh(y_pos, plot_df["valor_total"],
                        color=BAR_COLORS[: len(plot_df)], edgecolor="white", height=0.50)
        ax.set_yticks(y_pos)
        ax.set_yticklabels(plot_df["categoria"], fontsize=9)
        ax.set_xlabel("Valor (R$)", fontsize=10)
        ax.set_title("Ranking de Gastos por Categoria", fontsize=12, fontweight="bold")
        ax.grid(axis="x", linestyle="--", alpha=0.25)

        for bar, val in zip(bars, plot_df["valor_total"]):
            ax.text(
                bar.get_width() + bar.get_width() * 0.01,
                bar.get_y() + bar.get_height() / 2,
                format_currency(val), va="center", ha="left", fontsize=8,
            )
        for spine in ["top", "right"]:
            ax.spines[spine].set_visible(False)

    fig.tight_layout()
    fig.savefig(buffer, format="png", dpi=180, bbox_inches="tight")
    plt.close(fig)
    buffer.seek(0)
    return buffer

# ---------------------------------------------------------------------------
# ESTILOS PDF
# ---------------------------------------------------------------------------

def build_styles():
    styles = getSampleStyleSheet()

    defs = [
        # name              parent      font               sz  lead  color     align      sb  sa
        ("TitleDark",    "Heading1", "Helvetica-Bold",   20, 24, "#0F172A", TA_LEFT,    0,  4),
        ("SectionDark",  "Heading2", "Helvetica-Bold",   12, 15, "#0F172A", TA_LEFT,    6,  6),
        ("BodySmall",    "BodyText", "Helvetica",          9, 12, "#334155", TA_LEFT,    0,  4),
        ("SubHeader",    "BodyText", "Helvetica",         8,  11, "#64748B", TA_LEFT,    0,  2),
        # Cards
        ("CardLabel",    "BodyText", "Helvetica-Bold",   10, 13, "#FFFFFF", TA_LEFT,    0,  2),
        ("CardSubtitle", "BodyText", "Helvetica",          8, 10, "#E2E8F0", TA_LEFT,    0,  2),
        ("CardValue",    "BodyText", "Helvetica-Bold",   14, 17, "#FFFFFF", TA_LEFT,    3,  2),
        ("CardIcon",     "BodyText", "Helvetica-Bold",   20, 22, "#FFFFFF", TA_CENTER,  0,  2),
        ("CardLine2",    "BodyText", "Helvetica-Bold",   12, 15, "#FFFFFF", TA_LEFT,    0,  2),
        # Tabelas
        ("TableCell",    "BodyText", "Helvetica",          7,  9, "#1E293B", TA_LEFT,    0,  0),
        ("TableCellSm",  "BodyText", "Helvetica",          6,  8, "#1E293B", TA_LEFT,    0,  0),  # fonte menor
        ("TableCellBold","BodyText", "Helvetica-Bold",     7,  9, "#FFFFFF", TA_LEFT,    0,  0),
        ("TableCellR",   "BodyText", "Helvetica",          7,  9, "#1E293B", TA_RIGHT,   0,  0),
        ("TableCellRSm", "BodyText", "Helvetica",          6,  8, "#1E293B", TA_RIGHT,   0,  0),  # fonte menor alinhada à direita
        ("FooterStyle",  "BodyText", "Helvetica",          7,  9, "#94A3B8", TA_CENTER,  0,  0),
        ("HeaderStyle",  "BodyText", "Helvetica",          8, 10, "#475569", TA_LEFT,    0,  0),
    ]

    for name, parent, font, size, leading, color, align, sb, sa in defs:
        styles.add(ParagraphStyle(
            name=name, parent=styles[parent],
            fontName=font, fontSize=size, leading=leading,
            textColor=colors.HexColor(color), alignment=align,
            spaceBefore=sb, spaceAfter=sa,
        ))
    return styles

# ---------------------------------------------------------------------------
# HEADER / FOOTER
# ---------------------------------------------------------------------------

REPORT_METADATA_HOLDER: dict = {}


def _draw_header_footer(canvas, doc):
    meta        = REPORT_METADATA_HOLDER
    banco       = meta.get("banco", "")
    period      = meta.get("period", "")
    arq         = meta.get("arquivo", "")
    now         = meta.get("generated_at", "")
    total_pages = meta.get("total_pages", "?")

    W, H = landscape(A4)
    canvas.saveState()

    canvas.setStrokeColor(colors.HexColor("#0F172A"))
    canvas.setLineWidth(1.2)
    canvas.line(1.0 * cm, H - 0.7 * cm, W - 1.0 * cm, H - 0.7 * cm)

    canvas.setFont("Helvetica-Bold", 8)
    canvas.setFillColor(colors.HexColor("#0F172A"))
    canvas.drawString(1.0 * cm, H - 0.55 * cm, f"|  {banco}  |  Período: {period}")

    canvas.setFont("Helvetica", 7)
    canvas.setFillColor(colors.HexColor("#64748B"))
    canvas.drawRightString(W - 1.0 * cm, H - 0.55 * cm,
                           f"Arquivo: {arq}  |  Gerado em: {now}")

    canvas.setStrokeColor(colors.HexColor("#CBD5E1"))
    canvas.setLineWidth(0.5)
    canvas.line(1.0 * cm, 0.6 * cm, W - 1.0 * cm, 0.6 * cm)

    canvas.setFont("Helvetica", 7)
    canvas.setFillColor(colors.HexColor("#94A3B8"))
    canvas.drawCentredString(
        W / 2, 0.35 * cm,
        f"·  Relatório Gerencial de Fluxo de Caixa  ·  "
        f"Página {doc.page} de {total_pages}  ·  {now}",
    )
    canvas.restoreState()

# ---------------------------------------------------------------------------
# COMPONENTE DE CARD
# ---------------------------------------------------------------------------

def create_metric_card(
    icon: str,
    label: str,
    line1: str,
    line2: str,
    subtitle: str,
    color_hex: str,
    styles,
    value_color: str = "#FFFFFF",
) -> Table:
    icon_p  = Paragraph(sanitize_for_pdf(icon),     styles["CardIcon"])
    label_p = Paragraph(sanitize_for_pdf(label),    styles["CardLabel"])
    sub_p   = Paragraph(sanitize_for_pdf(subtitle), styles["CardSubtitle"])

    val_style = ParagraphStyle(
        "CardValDyn", parent=styles["CardValue"],
        textColor=colors.HexColor(value_color),
    )
    line1_p = Paragraph(sanitize_for_pdf(line1), val_style)

    content_col = [label_p, line1_p]
    if line2:
        line2_style = ParagraphStyle(
            "CardLine2Dyn", parent=styles["CardLine2"],
            textColor=colors.HexColor(value_color),
        )
        content_col.append(Paragraph(sanitize_for_pdf(line2), line2_style))
    content_col.append(sub_p)

    inner = Table([[icon_p, content_col]], colWidths=[1.3 * cm, 7.2 * cm])
    inner.setStyle(TableStyle([
        ("VALIGN",        (0, 0), (-1, -1), "MIDDLE"),
        ("LEFTPADDING",   (0, 0), (-1, -1), 0),
        ("RIGHTPADDING",  (0, 0), (-1, -1), 0),
        ("TOPPADDING",    (0, 0), (-1, -1), 0),
        ("BOTTOMPADDING", (0, 0), (-1, -1), 0),
    ]))

    outer = Table([[inner]], colWidths=[8.8 * cm])
    outer.setStyle(TableStyle([
        ("BACKGROUND",     (0, 0), (-1, -1), colors.HexColor(color_hex)),
        ("LEFTPADDING",    (0, 0), (-1, -1), 12),
        ("RIGHTPADDING",   (0, 0), (-1, -1), 10),
        ("TOPPADDING",     (0, 0), (-1, -1), 11),
        ("BOTTOMPADDING",  (0, 0), (-1, -1), 11),
        ("ROUNDEDCORNERS", (0, 0), (-1, -1), [5, 5, 5, 5]),
    ]))
    return outer

# ---------------------------------------------------------------------------
# GRID DE CARDS — 3 COLUNAS TEMÁTICAS
# ---------------------------------------------------------------------------

def create_summary_cards(metrics: dict, styles) -> Table:
    m = metrics

    cob_val   = m["indice_cobertura"]
    cob_color = "#059669" if cob_val >= 1.0 else "#DC2626"
    saldo       = m["saldo_periodo"]
    saldo_color = "#4ADE80" if saldo >= 0 else "#FCA5A5"

    # COL 1 — ENTRADAS
    col1 = [
        create_metric_card("↑", "Total de Entradas",
                           format_currency(m["total_entradas"]), "",
                           CARD_SUBTITLES["total_entradas"], "#059669", styles),
        create_metric_card("↑", "Ticket Médio de Entrada",
                           format_currency(m["ticket_medio_entrada"]), "",
                           CARD_SUBTITLES["ticket_medio_entrada"], "#047857", styles),
        create_metric_card("↑", "Maior Recebimento",
                           m["dia_maior_recebimento"],
                           format_currency(m["valor_maior_recebimento"]),
                           CARD_SUBTITLES["dia_maior_recebimento"], "#059669", styles),
    ]

    # COL 2 — SAÍDAS
    col2 = [
        create_metric_card("↓", "Total de Saídas",
                           format_currency(m["total_saidas"]), "",
                           CARD_SUBTITLES["total_saidas"], "#DC2626", styles),
        create_metric_card("↓", "Ticket Médio de Saída",
                           format_currency(m["ticket_medio_saida"]), "",
                           CARD_SUBTITLES["ticket_medio_saida"], "#B91C1C", styles),
        create_metric_card("↓", "Maior Pagamento",
                           m["dia_maior_pagamento"],
                           format_currency(m["valor_maior_pagamento"]),
                           CARD_SUBTITLES["dia_maior_pagamento"], "#DC2626", styles),
    ]

    # COL 3 — ÍNDICES NEUTROS (sem Qtd. de Transações)
    col3 = [
        create_metric_card("⚖", "Fluxo Líquido do Período",
                           format_currency(saldo), "",
                           CARD_SUBTITLES["saldo_periodo"], "#2563EB", styles, saldo_color),
        create_metric_card("◈", "Índice de Cobertura",
                           format_number(cob_val) + "x", "",
                           CARD_SUBTITLES["indice_cobertura"], cob_color, styles),
        create_metric_card("↑↓", "Transferências Internas",
                           format_percent(m["percentual_transferencias"]), "",
                           CARD_SUBTITLES["percentual_transferencias"], "#475569", styles),
        create_metric_card("⚠", "Dias com Pressão de Caixa",
                           str(m["dias_pressao_caixa"]) + " dias", "",
                           CARD_SUBTITLES["dias_pressao_caixa"], "#B45309", styles),
    ]

    n_rows = max(len(col1), len(col2), len(col3))
    V_GAP  = 0.45 * cm
    COL_W  = 9.1 * cm
    H_GAP  = 0.25 * cm

    def _pad(col, n):
        while len(col) < n:
            col.append(Spacer(COL_W, 0.1 * cm))
        return col

    col1, col2, col3 = _pad(col1, n_rows), _pad(col2, n_rows), _pad(col3, n_rows)

    table_rows = []
    for i in range(n_rows):
        table_rows.append([col1[i], col2[i], col3[i]])
        if i < n_rows - 1:
            table_rows.append([Spacer(1, V_GAP)] * 3)

    grid = Table(table_rows, colWidths=[COL_W + H_GAP] * 3, hAlign="LEFT")
    grid.setStyle(TableStyle([
        ("LEFTPADDING",   (0, 0), (-1, -1), 0),
        ("RIGHTPADDING",  (0, 0), (-1, -1), 0),
        ("TOPPADDING",    (0, 0), (-1, -1), 0),
        ("BOTTOMPADDING", (0, 0), (-1, -1), 0),
        ("VALIGN",        (0, 0), (-1, -1), "TOP"),
    ]))
    return grid

# ---------------------------------------------------------------------------
# TABELAS PDF
# ---------------------------------------------------------------------------

def dataframe_to_pdf_table(
    df: pd.DataFrame,
    columns: list,
    headers: list,
    widths: list,
    styles,
    wrap_cols: set = None,
    right_align_cols: set = None,
    highlight_negative_flow: bool = False,
    extra_row_styles: list = None,
    small_font: bool = False,          # ← novo parâmetro
) -> Table:
    wrap_cols        = set(wrap_cols        or [])
    right_align_cols = set(right_align_cols or [])

    # Escolhe estilos de célula conforme tamanho solicitado
    cell_style_l = styles["TableCellSm"]  if small_font else styles["TableCell"]
    cell_style_r = styles["TableCellRSm"] if small_font else styles["TableCellR"]

    header_cells = [
        Paragraph(f"<b>{sanitize_for_pdf(str(h))}</b>", styles["TableCellBold"])
        for h in headers
    ]

    if df.empty:
        empty_row    = ["-"] * len(headers)
        empty_row[0] = "Sem dados"
        rows = [header_cells,
                [Paragraph(sanitize_for_pdf(v), cell_style_l) for v in empty_row]]
    else:
        body_rows = []
        for _, row in df.iterrows():
            cells = []
            for col in columns:
                val = row[col]
                if isinstance(val, (int, float)):
                    if "percentual" in col:
                        text = format_percent(float(val))
                    elif any(k in col for k in ("valor", "entradas", "saidas", "fluxo", "saldo")):
                        text = format_currency(float(val))
                    else:
                        text = str(int(val)) if float(val) == int(float(val)) else format_number(float(val))
                elif hasattr(val, "strftime"):
                    text = val.strftime("%d/%m/%Y")
                else:
                    text = str(val)
                st = cell_style_r if col in right_align_cols else cell_style_l
                cells.append(Paragraph(sanitize_for_pdf(text), st))
            body_rows.append(cells)
        rows = [header_cells] + body_rows

    table = Table(rows, colWidths=widths, repeatRows=1, splitByRow=1)

    base_style = [
        ("BACKGROUND",     (0, 0), (-1,  0), colors.HexColor("#0F172A")),
        ("TEXTCOLOR",      (0, 0), (-1,  0), colors.white),
        ("GRID",           (0, 0), (-1, -1), 0.3, colors.HexColor("#CBD5E1")),
        ("ROWBACKGROUNDS", (0, 1), (-1, -1), [colors.white, colors.HexColor("#F8FAFC")]),
        ("VALIGN",         (0, 0), (-1, -1), "TOP"),
        ("LEFTPADDING",    (0, 0), (-1, -1), 5),
        ("RIGHTPADDING",   (0, 0), (-1, -1), 5),
        ("TOPPADDING",     (0, 0), (-1, -1), 3),
        ("BOTTOMPADDING",  (0, 0), (-1, -1), 3),
    ]

    if highlight_negative_flow and not df.empty and "fluxo_liquido" in df.columns:
        for i, (_, row) in enumerate(df.iterrows(), start=1):
            if float(row.get("fluxo_liquido", 0)) < 0:
                base_style.append(
                    ("BACKGROUND", (0, i), (-1, i), colors.HexColor("#FEE2E2"))
                )

    if extra_row_styles:
        base_style.extend(extra_row_styles)

    table.setStyle(TableStyle(base_style))
    return table

# ---------------------------------------------------------------------------
# PÁGINAS DO PDF
# ---------------------------------------------------------------------------

def build_page_executive(story: list, metrics: dict, metadata: dict, styles):
    """Página 1 — Resumo Executivo: qtd. transações no subtítulo, sem card."""
    periodo = (
        f"{metadata.get('inicio_extrato', '')[:10]} a {metadata.get('fim_extrato', '')[:10]}"
        if metadata.get("inicio_extrato") or metadata.get("fim_extrato")
        else "Não informado"
    )
    qtd = metadata.get("quantidade_transacoes", metrics.get("quantidade_transacoes", 0))

    story.append(Spacer(1, 0.4 * cm))
    story.append(Paragraph("Relatório Gerencial de Fluxo de Caixa", styles["TitleDark"]))

    # Linha de subtítulo: banco | período | qtd. transações
    story.append(Paragraph(
        f"<b>{sanitize_for_pdf(metadata.get('banco', 'Banco não identificado'))}</b>"
        f"&nbsp;&nbsp;|&nbsp;&nbsp;Período: {sanitize_for_pdf(periodo)}"
        f"&nbsp;&nbsp;|&nbsp;&nbsp;{qtd} transações registradas",
        styles["SubHeader"],
    ))
    story.append(HRFlowable(width="100%", thickness=0.5,
                            color=colors.HexColor("#CBD5E1"), spaceAfter=10))
    story.append(Paragraph("Resumo Executivo", styles["SectionDark"]))
    story.append(Spacer(1, 0.25 * cm))
    story.append(create_summary_cards(metrics, styles))


def build_page_charts(story: list, daily_df: pd.DataFrame,
                      category_df: pd.DataFrame, styles):
    """Página 2 — Dashboard de Gráficos."""
    story.append(PageBreak())
    story.append(Spacer(1, 0.3 * cm))
    story.append(Paragraph("Dashboard de Gráficos do Período", styles["SectionDark"]))
    story.append(HRFlowable(width="100%", thickness=0.5,
                            color=colors.HexColor("#CBD5E1"), spaceAfter=6))

    # ── Gráfico diário — ocupa toda a largura ───────────────────────────────
    # fig gerada: 15x5.5 → razão = 5.5/15 = 0.3667
    # largura disponível em landscape A4 c/ margens: ~27 cm
    daily_w = 27.0 * cm
    daily_h = daily_w * (5.5 / 15.0)   # mantém proporção exata
    chart_daily = draw_chart_daily(daily_df)
    story.append(Paragraph("Entradas × Saídas por Dia  |  Saldo Acumulado",
                            styles["BodySmall"]))
    story.append(Image(chart_daily, width=daily_w, height=daily_h))
    story.append(Spacer(1, 0.4 * cm))

    # ── Pie + Bar lado a lado ────────────────────────────────────────────────
    # Cada coluna: ~13 cm de largura disponível (27 cm / 2 - gap)
    col_w = 13.0 * cm

    # pie: fig 6.5x6.5 (quadrada) → proporção 1:1
    pie_w = col_w
    pie_h = pie_w * (6.5 / 6.5)   # = col_w (quadrado perfeito)

    # bar: fig 8.5 x fig_height (calculada dinamicamente em draw_chart_categories_bar)
    # usamos a razão base: 8.5 x 5.5 (caso médio de 5 barras → height ~5.5)
    bar_w = col_w
    bar_h = bar_w * (5.5 / 8.5)

    chart_pie = draw_chart_categories_pie(category_df)
    chart_bar = draw_chart_categories_bar(category_df)

    charts_row = Table(
        [[
            Image(chart_pie, width=pie_w, height=pie_h),
            Image(chart_bar, width=bar_w, height=bar_h),
        ]],
        colWidths=[col_w + 0.5 * cm, col_w + 0.5 * cm],
    )
    charts_row.setStyle(TableStyle([
        ("VALIGN",        (0, 0), (-1, -1), "MIDDLE"),
        ("LEFTPADDING",   (0, 0), (-1, -1), 0),
        ("RIGHTPADDING",  (0, 0), (-1, -1), 4),
        ("TOPPADDING",    (0, 0), (-1, -1), 0),
        ("BOTTOMPADDING", (0, 0), (-1, -1), 0),
    ]))
    story.append(charts_row)



def build_page_detail(
    story: list,
    df: pd.DataFrame,
    daily_df: pd.DataFrame,
    category_df: pd.DataFrame,
    income_category_df: pd.DataFrame,
    maiores_entradas: pd.DataFrame,
    maiores_saidas: pd.DataFrame,
    inconsistencies: list,
    styles,
):
    """Página 3+ — Detalhamento Analítico completo."""
    story.append(PageBreak())
    story.append(Spacer(1, 0.3 * cm))
    story.append(Paragraph("Detalhamento Analítico", styles["SectionDark"]))
    story.append(HRFlowable(width="100%", thickness=0.5,
                            color=colors.HexColor("#CBD5E1"), spaceAfter=6))

    # ── Categorias de Entradas ───────────────────────────────────────────────
    story.append(Paragraph("Categorias de Entradas", styles["BodySmall"]))
    story.append(dataframe_to_pdf_table(
        income_category_df,
        columns=["categoria", "valor_total", "quantidade_transacoes", "participacao_percentual"],
        headers=["Categoria", "Valor Total", "Qtd.", "%"],
        widths=[11.0 * cm, 5.0 * cm, 2.5 * cm, 4.5 * cm],
        styles=styles,
        wrap_cols={"categoria"},
        right_align_cols={"valor_total", "participacao_percentual"},
    ))
    story.append(Spacer(1, 0.3 * cm))

    # ── Categorias de Despesas ───────────────────────────────────────────────
    story.append(Paragraph("Categorias de Despesas", styles["BodySmall"]))
    story.append(dataframe_to_pdf_table(
        category_df,
        columns=["categoria", "valor_total", "quantidade_transacoes", "participacao_percentual"],
        headers=["Categoria", "Valor Total", "Qtd.", "%"],
        widths=[11.0 * cm, 5.0 * cm, 2.5 * cm, 4.5 * cm],
        styles=styles,
        wrap_cols={"categoria"},
        right_align_cols={"valor_total", "participacao_percentual"},
    ))
    story.append(Spacer(1, 0.3 * cm))

    # ── Top 5 Entradas ───────────────────────────────────────────────────────
    story.append(Paragraph("Top 5 Maiores Entradas", styles["BodySmall"]))
    ent_pdf = maiores_entradas[["data", "descricao", "valor", "categoria"]].copy() \
        if not maiores_entradas.empty else pd.DataFrame()
    if not ent_pdf.empty:
        ent_pdf["data"] = pd.to_datetime(ent_pdf["data"])
    story.append(dataframe_to_pdf_table(
        ent_pdf,
        columns=["data", "descricao", "valor", "categoria"],
        headers=["Data", "Descrição", "Valor", "Categoria"],
        widths=[2.5 * cm, 14.5 * cm, 3.5 * cm, 6.5 * cm],
        styles=styles,
        wrap_cols={"descricao", "categoria"},
        right_align_cols={"valor"},
    ))
    story.append(Spacer(1, 0.3 * cm))

    # ── Top 5 Saídas ─────────────────────────────────────────────────────────
    story.append(Paragraph("Top 5 Maiores Saídas", styles["BodySmall"]))
    sai_pdf = maiores_saidas[["data", "descricao", "valor", "categoria"]].copy() \
        if not maiores_saidas.empty else pd.DataFrame()
    if not sai_pdf.empty:
        sai_pdf["data"] = pd.to_datetime(sai_pdf["data"])
    story.append(dataframe_to_pdf_table(
        sai_pdf,
        columns=["data", "descricao", "valor", "categoria"],
        headers=["Data", "Descrição", "Valor", "Categoria"],
        widths=[2.5 * cm, 14.5 * cm, 3.5 * cm, 6.5 * cm],
        styles=styles,
        wrap_cols={"descricao", "categoria"},
        right_align_cols={"valor"},
    ))
    story.append(Spacer(1, 0.3 * cm))

    # ── Transações Não Classificadas (fonte menor) ───────────────────────────
    nao_class = df[df["categoria"].isin(UNCLASSIFIED_CATEGORIES)].copy() \
        if not df.empty else pd.DataFrame()
    if not nao_class.empty:
        story.append(Paragraph(
            f"Transações Não Classificadas  ({len(nao_class)} registros — revisão recomendada)",
            styles["BodySmall"],
        ))
        nao_display = nao_class.head(20)[["data", "descricao", "valor", "categoria"]].copy()
        nao_display["data"] = pd.to_datetime(nao_display["data"])
        yellow_styles = [
            ("BACKGROUND", (0, i), (-1, i), colors.HexColor("#FEFCE8"))
            for i in range(1, len(nao_display) + 1)
        ]
        story.append(dataframe_to_pdf_table(
            nao_display,
            columns=["data", "descricao", "valor", "categoria"],
            headers=["Data", "Descrição", "Valor", "Categoria"],
            widths=[2.5 * cm, 14.5 * cm, 3.5 * cm, 6.5 * cm],
            styles=styles,
            wrap_cols={"descricao", "categoria"},
            right_align_cols={"valor"},
            extra_row_styles=yellow_styles,
            small_font=True,           # ← fonte levemente menor
        ))
        story.append(Spacer(1, 0.3 * cm))

    # ── Observações ──────────────────────────────────────────────────────────
    story.append(Paragraph("Observações e Inconsistências", styles["BodySmall"]))
    obs = [
        f"• Transações não classificadas automaticamente: {len(nao_class) if not nao_class.empty else 0}",
        f"• Inconsistências detectadas: {len(inconsistencies)}",
        "• Canais genéricos (PIX, TED, DOC, compras sem complemento) foram consolidados como não classificados.",
    ]
    if inconsistencies:
        obs += [f"  — {item}" for item in inconsistencies[:5]]
    for line in obs:
        story.append(Paragraph(sanitize_for_pdf(line), styles["BodySmall"]))

# ---------------------------------------------------------------------------
# GERAÇÃO DO PDF
# ---------------------------------------------------------------------------

def generate_pdf_report(file_path: Path, df: pd.DataFrame,
                        metadata: dict, inconsistencies: list) -> Path:
    timestamp   = datetime.now().strftime("%Y%m%d_%H%M%S")
    output_file = OUTPUT_DIR / f"relatorio_{file_path.stem}_{timestamp}.pdf"

    metrics                          = build_indicator_dict(df)
    daily_df                         = build_daily_summary(df)
    category_df                      = build_category_summary(df)
    income_category_df               = build_income_category_summary(df)
    maiores_entradas, maiores_saidas = build_top_movements(df)

    periodo = (
        f"{metadata.get('inicio_extrato', '')[:10]} a {metadata.get('fim_extrato', '')[:10]}"
        if metadata.get("inicio_extrato") or metadata.get("fim_extrato")
        else "Não informado"
    )

    REPORT_METADATA_HOLDER.update({
        "banco":        metadata.get("banco", "Banco não identificado"),
        "period":       periodo,
        "arquivo":      metadata.get("arquivo", "-"),
        "generated_at": datetime.now().strftime("%d/%m/%Y %H:%M"),
        "total_pages":  "?",   # provisório durante o 1º build
    })

    styles = build_styles()

    def _build_story():
        story = []
        build_page_executive(story, metrics, metadata, styles)
        build_page_charts(story, daily_df, category_df, styles)
        build_page_detail(
            story, df, daily_df, category_df, income_category_df,
            maiores_entradas, maiores_saidas, inconsistencies, styles,
        )
        return story

    doc = SimpleDocTemplate(
        str(output_file),
        pagesize=landscape(A4),
        rightMargin=1.0 * cm,
        leftMargin=1.0 * cm,
        topMargin=1.2 * cm,
        bottomMargin=1.2 * cm,
        allowSplitting=1,
    )

    # ── 1º build: descobre quantas páginas reais foram geradas ──────────────
    doc.build(_build_story(),
              onFirstPage=_draw_header_footer,
              onLaterPages=_draw_header_footer)

    real_pages = doc.page   # ReportLab expõe o total real aqui

    # ── 2º build: agora com total_pages correto no rodapé ───────────────────
    REPORT_METADATA_HOLDER["total_pages"] = real_pages

    doc2 = SimpleDocTemplate(
        str(output_file),
        pagesize=landscape(A4),
        rightMargin=1.0 * cm,
        leftMargin=1.0 * cm,
        topMargin=1.2 * cm,
        bottomMargin=1.2 * cm,
        allowSplitting=1,
    )
    doc2.build(_build_story(),
               onFirstPage=_draw_header_footer,
               onLaterPages=_draw_header_footer)

    return output_file


# ---------------------------------------------------------------------------
# EXPORTAÇÃO
# ---------------------------------------------------------------------------

def export_results(file_path: Path, df: pd.DataFrame,
                   metadata: dict, inconsistencies: list) -> dict:
    timestamp  = datetime.now().strftime("%Y%m%d_%H%M%S")
    excel_file = OUTPUT_DIR / f"resultado_{file_path.stem}_{timestamp}.xlsx"

    indicators_df            = build_indicators(df)
    metadata_df              = pd.DataFrame([metadata])
    nao_class                = df[df["categoria"].isin(UNCLASSIFIED_CATEGORIES)] \
                               if not df.empty else pd.DataFrame()
    inconsist_df             = pd.DataFrame([{"inconsistencia": i} for i in inconsistencies]) \
                               if inconsistencies else pd.DataFrame([{"inconsistencia": "Nenhuma"}])
    maiores_ent, maiores_sai = build_top_movements(df)
    daily_df                 = build_daily_summary(df)
    category_df              = build_category_summary(df)
    income_category_df       = build_income_category_summary(df)

    with pd.ExcelWriter(excel_file, engine="openpyxl") as writer:
        metadata_df.to_excel(writer,        sheet_name="metadados",           index=False)
        df.to_excel(writer,                 sheet_name="transacoes",           index=False)
        indicators_df.to_excel(writer,      sheet_name="indicadores",          index=False)
        daily_df.to_excel(writer,           sheet_name="fluxo_diario",         index=False)
        category_df.to_excel(writer,        sheet_name="categorias_despesa",   index=False)
        income_category_df.to_excel(writer, sheet_name="categorias_entrada",   index=False)
        maiores_ent.to_excel(writer,        sheet_name="maiores_entradas",      index=False)
        maiores_sai.to_excel(writer,        sheet_name="maiores_saidas",        index=False)
        inconsist_df.to_excel(writer,       sheet_name="inconsistencias",       index=False)
        nao_class.to_excel(writer,          sheet_name="nao_classificadas",     index=False)

    pdf_file = generate_pdf_report(file_path, df, metadata, inconsistencies)
    return {"excel": excel_file, "pdf": pdf_file}

def send_email_with_attachments(file_path: Path, outputs: dict, metadata: dict):
    smtp_host = os.getenv("SMTP_HOST")
    smtp_port = int(os.getenv("SMTP_PORT", "587"))
    smtp_user = os.getenv("SMTP_USER")
    smtp_password = os.getenv("SMTP_PASSWORD")
    smtp_from = os.getenv("SMTP_FROM")
    smtp_to = os.getenv("SMTP_TO")

    if not all([smtp_host, smtp_user, smtp_password, smtp_from, smtp_to]):
        raise ValueError("Variáveis SMTP ausentes no .env.")

    msg = EmailMessage()
    msg["Subject"] = f"Seu Relatório Gerencial de Fluxo de Caixa está pronto!"
    msg["From"] = smtp_from
    msg["To"] = smtp_to

    msg.set_content(
                "Prezado(a),\n\n"
    "O processamento do arquivo OFX foi concluído com sucesso.\n\n"
    "Segue em anexo o Relatório Gerencial de Fluxo de Caixa, elaborado com base no extrato processado.\n\n"
    "O material apresenta uma visão consolidada das movimentações financeiras do período, incluindo indicadores relevantes para apoio à análise gerencial e à tomada de decisão.\n\n"
    f"Banco analisado: {metadata.get('banco', 'Não identificado')}\n"
    f"Quantidade de transações analisadas: {metadata.get('quantidade_transacoes', 0)}\n\n"
    "No relatório, você encontrará informações como:\n"
    "• Total de entradas e saídas\n"
    "• Fluxo líquido do período\n"
    "• Índice de cobertura\n"
    "• Pressão de caixa\n"
    "• Maiores entradas e saídas\n"
    "• Classificação das movimentações\n\n"
    "O arquivo segue no formato PDF para consulta e apoio complementar.\n\n"
    )

    pdf_path = outputs["pdf"]

    with open(pdf_path, "rb") as f:
        file_data = f.read()

    msg.add_attachment(
        file_data,
        maintype="application",
        subtype="pdf",
        filename=pdf_path.name,
    )
    

    logging.info(f"Enviando e-mail para {smtp_to}...")

    with smtplib.SMTP(smtp_host, smtp_port) as server:
        server.ehlo()
        server.starttls()
        server.ehlo()
        server.login(smtp_user, smtp_password)
        server.send_message(msg)

    logging.info("E-mail enviado com sucesso.")
# ---------------------------------------------------------------------------
# PROCESSAMENTO
# ---------------------------------------------------------------------------

def process_ofx(file_path: Path):
    # ── Evita processamento duplo do mesmo arquivo ──
    with _processing_lock:
        if file_path.name in _files_in_process:
            logging.info(f"Já em processamento, ignorado: {file_path.name}")
            return
        _files_in_process.add(file_path.name)

    try:
        logging.info(f"Iniciando processamento: {file_path.name}")

        if file_path.suffix.lower() != ".ofx":
            logging.warning(f"Arquivo ignorado (não é OFX): {file_path.name}")
            return
        if not file_path.exists():
            logging.warning(f"Arquivo não encontrado: {file_path}")
            return
        if not wait_until_file_is_ready(file_path):
            logging.error(f"Arquivo não ficou pronto a tempo: {file_path.name}")
            if file_path.exists():
                move_with_unique_name(file_path, ERROR_DIR)
            return

        df, metadata, inconsistencies = parse_ofx(file_path)
        fatal_errors, inconsistencies = validate_parsed_ofx(df, metadata, inconsistencies)
        if fatal_errors:
            for err in fatal_errors:
                logging.error(f"Falha de validação OFX: {err}")
            if inconsistencies:
                for inc in inconsistencies:
                    logging.warning(f"Inconsistência OFX: {inc}")

            if file_path.exists():
                moved = move_with_unique_name(file_path, ERROR_DIR)
                logging.info(f"Arquivo movido para erros: {moved.name}")
            return

        outputs = export_results(file_path, df, metadata, inconsistencies)
        logging.info(f"Excel gerado: {outputs['excel'].name}")
        logging.info(f"PDF gerado:   {outputs['pdf'].name}")

        try:
            send_email_with_attachments(file_path, outputs, metadata)
        except Exception as email_error:
            logging.exception(f"Erro ao enviar e-mail de {file_path.name}: {email_error}")

            if file_path.exists():
                moved = move_with_unique_name(file_path, EMAIL_ERROR_DIR)
                logging.info(f"Arquivo movido para erros de e-mail: {moved.name}")
            return

        moved = move_with_unique_name(file_path, PROCESSED_DIR)
        logging.info(f"Arquivo movido para processados: {moved.name}")

    except Exception as e:
        logging.exception(f"Erro ao processar {file_path.name}: {e}")
        if file_path.exists():
            moved = move_with_unique_name(file_path, ERROR_DIR)
            logging.info(f"Arquivo movido para erros: {moved.name}")

    finally:
        # ── Libera o arquivo do controle independente do resultado ──
        with _processing_lock:
            _files_in_process.discard(file_path.name)


def scan_input_folder():
    files = sorted(INPUT_DIR.glob("*.ofx"))
    if files:
        logging.info(f"Varredura: {len(files)} arquivo(s) OFX encontrado(s).")
    for file_path in files:
        process_ofx(file_path)

# ---------------------------------------------------------------------------
# WATCHDOG
# ---------------------------------------------------------------------------

class OFXHandler(FileSystemEventHandler):
    def on_created(self, event):
        if event.is_directory:
            return
        file_path = Path(event.src_path)
        logging.info(f"Evento (created): {file_path.name}")
        if file_path.suffix.lower() == ".ofx":
            time.sleep(1)
            process_ofx(file_path)

    def on_moved(self, event):
        if hasattr(event, "dest_path"):
            file_path = Path(event.dest_path)
            logging.info(f"Evento (moved): {file_path.name}")
            if file_path.suffix.lower() == ".ofx":
                time.sleep(1)
                process_ofx(file_path)

    def on_modified(self, event):
        if event.is_directory:
            return
        file_path = Path(event.src_path)
        if file_path.suffix.lower() == ".ofx":
            logging.info(f"Evento (modified): {file_path.name}")
            time.sleep(1)
            process_ofx(file_path)

# ---------------------------------------------------------------------------
# MAIN
# ---------------------------------------------------------------------------

def main():
    setup_folders()
    setup_logging()

    logging.info("=" * 50)
    logging.info("RPA OFX iniciado")
    logging.info(f"Monitorando: {INPUT_DIR}")
    logging.info("Saída: Excel técnico + PDF gerencial.")
    logging.info(f"Varredura a cada {POLL_INTERVAL_SECONDS}s. CTRL+C para encerrar.")

    scan_input_folder()

    observer = Observer()
    observer.schedule(OFXHandler(), str(INPUT_DIR), recursive=False)
    observer.start()

    try:
        while True:
            time.sleep(POLL_INTERVAL_SECONDS)
            scan_input_folder()
    except KeyboardInterrupt:
        observer.stop()
    observer.join()
    logging.info("RPA OFX encerrado.")


if __name__ == "__main__":
    main()
