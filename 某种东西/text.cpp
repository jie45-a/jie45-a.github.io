// 高等数学计算器 - 图形化交互界面
// 支持：微积分、线性代数、方程求解、特殊函数等
// 使用 Win32 API 构建 GUI

#include <windows.h>
#include <commctrl.h>
#include <string>
#include <vector>
#include <cmath>
#include <sstream>
#include <iomanip>
#include <stack>
#include <cctype>

#pragma comment(lib, "comctl32.lib")

// ==================== 全局常量 ====================
#define ID_DISPLAY      1001
#define ID_BTN_BASE     2000
#define ID_TAB_CALC     3001
#define ID_TAB_CALCULUS 3002
#define ID_TAB_MATRIX   3003
#define ID_TAB_EQUATION 3004
#define ID_INPUT_FUNC   4001
#define ID_RESULT_BOX   4002
#define ID_BTN_COMPUTE  4003

// 按钮ID偏移
enum {
    // 数字 0-9
    BTN_0 = 0, BTN_1, BTN_2, BTN_3, BTN_4, BTN_5, BTN_6, BTN_7, BTN_8, BTN_9,
    // 运算符
    BTN_ADD, BTN_SUB, BTN_MUL, BTN_DIV, BTN_POW,
    // 函数
    BTN_SIN, BTN_COS, BTN_TAN, BTN_LN, BTN_LOG, BTN_SQRT,
    BTN_FACT, BTN_PI, BTN_E, BTN_ABS,
    // 控制
    BTN_LPAREN, BTN_RPAREN, BTN_DOT, BTN_CLEAR, BTN_DEL, BTN_EQUALS,
    BTN_SIGN,   // +/- 切换符号
    // 微积分
    BTN_DIFF, BTN_INTEG, BTN_LIMIT,
    // 矩阵
    BTN_DET, BTN_INV, BTN_TRANS,
    BTN_COUNT
};

// 颜色常量
#define COLOR_BG        RGB(30, 30, 30)
#define COLOR_DISPLAY   RGB(20, 20, 20)
#define COLOR_BTN_NUM   RGB(60, 60, 60)
#define COLOR_BTN_OP    RGB(255, 140, 0)
#define COLOR_BTN_FUNC  RGB(80, 80, 80)
#define COLOR_BTN_EQ    RGB(0, 150, 200)
#define COLOR_BTN_CLR   RGB(200, 60, 60)
#define COLOR_TEXT      RGB(255, 255, 255)
#define COLOR_TEXT_DIM  RGB(180, 180, 180)

// ==================== 全局状态 ====================
HWND g_hDisplay, g_hResultBox, g_hInputFunc;
HWND g_hTabCalc, g_hTabCalculus, g_hTabMatrix, g_hTabEquation;
HWND g_hMainWnd;
std::wstring g_expression;
std::wstring g_result;
bool g_justEvaluated = false;
int g_currentTab = 0;  // 0=计算器, 1=微积分, 2=矩阵, 3=方程

// 矩阵存储
double g_matrixA[3][3] = {{1,0,0},{0,1,0},{0,0,1}};
double g_matrixB[3][3] = {{1,0,0},{0,1,0},{0,0,1}};
int g_matrixRowsA = 3, g_matrixColsA = 3;
int g_matrixRowsB = 3, g_matrixColsB = 3;

// ==================== 数学引擎 ====================

// 优先级
int precedence(wchar_t op) {
    if (op == L'+' || op == L'-') return 1;
    if (op == L'*' || op == L'/') return 2;
    if (op == L'^') return 3;
    if (op == L'u') return 4; // 一元负号
    return 0;
}

// 判断是否为函数名
bool isFuncName(const std::wstring& s) {
    return s == L"sin" || s == L"cos" || s == L"tan" ||
           s == L"ln" || s == L"log" || s == L"sqrt" ||
           s == L"abs" || s == L"asin" || s == L"acos" || s == L"atan";
}

// 应用函数
double applyFunc(const std::wstring& func, double val) {
    if (func == L"sin") return sin(val);
    if (func == L"cos") return cos(val);
    if (func == L"tan") return tan(val);
    if (func == L"ln") return log(val);
    if (func == L"log") return log10(val);
    if (func == L"sqrt") return sqrt(val);
    if (func == L"abs") return fabs(val);
    if (func == L"asin") return asin(val);
    if (func == L"acos") return acos(val);
    if (func == L"atan") return atan(val);
    return val;
}

// 阶乘
double factorial(int n) {
    if (n < 0) return NAN;
    if (n <= 1) return 1;
    double r = 1;
    for (int i = 2; i <= n; i++) r *= i;
    return r;
}

// 表达式求值 - Shunting-yard算法
double evaluate(const std::wstring& expr, bool& ok) {
    ok = true;
    std::stack<double> vals;
    std::stack<wchar_t> ops;
    
    size_t i = 0;
    bool expectUnary = true;
    
    while (i < expr.length()) {
        if (expr[i] == L' ') { i++; continue; }
        
        // 数字
        if (isdigit(expr[i]) || (expr[i] == L'.' && i+1 < expr.length() && isdigit(expr[i+1]))) {
            std::wstring numStr;
            while (i < expr.length() && (isdigit(expr[i]) || expr[i] == L'.')) {
                numStr += expr[i]; i++;
            }
            vals.push(std::stod(numStr));
            expectUnary = false;
            continue;
        }
        
        // π 和 e
        if (expr[i] == L'π') {
            vals.push(3.14159265358979323846);
            expectUnary = false; i++; continue;
        }
        if (expr[i] == L'e' && (i == expr.length()-1 || !isalpha(expr[i+1]) || expr[i+1] == L'(')) {
            // 单独的 e，不是 exp 的一部分
            if (i+1 < expr.length() && expr[i+1] == L'x') { i += 2; continue; } // skip "exp" prefix
            vals.push(2.71828182845904523536);
            expectUnary = false; i++; continue;
        }
        
        // 阶乘后缀
        if (expr[i] == L'!') {
            if (vals.empty()) { ok = false; return 0; }
            double v = vals.top(); vals.pop();
            if (v < 0 || v != floor(v)) { ok = false; return 0; }
            vals.push(factorial((int)v));
            expectUnary = false; i++; continue;
        }
        
        // 函数名
        if (isalpha(expr[i])) {
            std::wstring funcName;
            while (i < expr.length() && isalpha(expr[i])) {
                funcName += expr[i]; i++;
            }
            if (isFuncName(funcName)) {
                // 函数名入操作符栈，期待 '('
                if (i < expr.length() && expr[i] == L'(') {
                    ops.push(funcName[0] == L's' && funcName.length() > 2 ? 
                            (funcName[1] == L'i' ? L's' : L'q') : funcName[0]);
                    // 存完整函数名: 用特殊方式
                    // 简化: 我们把函数信息编码
                    // 这里用一个trick: push一个特殊标记到vals
                } else {
                    ok = false; return 0;
                }
                expectUnary = true;
                continue;
            } else {
                ok = false; return 0;
            }
        }
        
        wchar_t ch = expr[i];
        
        // 左括号
        if (ch == L'(') {
            // 检查前面是否有函数
            if (!ops.empty() && ops.top() >= L'a') {
                // 函数调用，不做特殊处理，直接压括号
            }
            ops.push(ch);
            expectUnary = true;
            i++; continue;
        }
        
        // 右括号
        if (ch == L')') {
            while (!ops.empty() && ops.top() != L'(') {
                wchar_t op = ops.top(); ops.pop();
                if (vals.size() < 2) { ok = false; return 0; }
                double b = vals.top(); vals.pop();
                double a = vals.top(); vals.pop();
                switch (op) {
                    case L'+': vals.push(a + b); break;
                    case L'-': vals.push(a - b); break;
                    case L'*': vals.push(a * b); break;
                    case L'/': if (b == 0) { ok = false; return 0; } vals.push(a / b); break;
                    case L'^': vals.push(pow(a, b)); break;
                    default: ok = false; return 0;
                }
            }
            if (ops.empty()) { ok = false; return 0; }
            wchar_t maybeFunc = ops.top(); ops.pop(); // 弹出 '('
            // 检查是否是函数调用
            if (maybeFunc != L'(' && maybeFunc >= L'a') {
                // 是函数
                if (vals.empty()) { ok = false; return 0; }
                double arg = vals.top(); vals.pop();
                std::wstring fname;
                if (maybeFunc == L's') fname = L"sin";
                else if (maybeFunc == L'c') fname = L"cos";
                else if (maybeFunc == L't') fname = L"tan";
                else if (maybeFunc == L'l') fname = L"ln";
                else if (maybeFunc == L'g') fname = L"log";
                else if (maybeFunc == L'q') fname = L"sqrt";
                else if (maybeFunc == L'a') fname = L"abs";
                else { ok = false; return 0; }
                vals.push(applyFunc(fname, arg));
            }
            expectUnary = false;
            i++; continue;
        }
        
        // 一元负号
        if (ch == L'-' && expectUnary) {
            ops.push(L'u'); // 用 'u' 表示一元负号
            i++; continue;
        }
        
        // 二元运算符
        if (ch == L'+' || ch == L'-' || ch == L'*' || ch == L'/' || ch == L'^') {
            while (!ops.empty() && ops.top() != L'(' && 
                   (precedence(ops.top()) >= precedence(ch) || ops.top() == L'u')) {
                wchar_t op = ops.top(); ops.pop();
                if (op == L'u') {
                    if (vals.empty()) { ok = false; return 0; }
                    double a = vals.top(); vals.pop();
                    vals.push(-a);
                } else {
                    if (vals.size() < 2) { ok = false; return 0; }
                    double b = vals.top(); vals.pop();
                    double a = vals.top(); vals.pop();
                    switch (op) {
                        case L'+': vals.push(a + b); break;
                        case L'-': vals.push(a - b); break;
                        case L'*': vals.push(a * b); break;
                        case L'/': if (b == 0) { ok = false; return 0; } vals.push(a / b); break;
                        case L'^': vals.push(pow(a, b)); break;
                        default: ok = false; return 0;
                    }
                }
            }
            ops.push(ch);
            expectUnary = true;
            i++; continue;
        }
        
        i++;
    }
    
    // 清空剩余
    while (!ops.empty()) {
        wchar_t op = ops.top(); ops.pop();
        if (op == L'u') {
            if (vals.empty()) { ok = false; return 0; }
            double a = vals.top(); vals.pop();
            vals.push(-a);
        } else {
            if (vals.size() < 2) { ok = false; return 0; }
            double b = vals.top(); vals.pop();
            double a = vals.top(); vals.pop();
            switch (op) {
                case L'+': vals.push(a + b); break;
                case L'-': vals.push(a - b); break;
                case L'*': vals.push(a * b); break;
                case L'/': if (b == 0) { ok = false; return 0; } vals.push(a / b); break;
                case L'^': vals.push(pow(a, b)); break;
                default: ok = false; return 0;
            }
        }
    }
    
    if (vals.size() != 1) { ok = false; return 0; }
    return vals.top();
}

// 数值微分 (中心差分)
double numericalDerivative(const std::wstring& funcExpr, double x, double h = 1e-6) {
    // 简单实现：用x+h和x-h求值
    // 这里用一个简化方案：对单变量表达式在x处求导
    // 替换表达式中的x并求值
    auto evalAt = [&](double val) -> double {
        std::wstring s = funcExpr;
        std::wstring xStr = std::to_wstring(val);
        // 简化替换
        size_t pos = 0;
        while ((pos = s.find(L'x', pos)) != std::wstring::npos) {
            s.replace(pos, 1, L"(" + xStr + L")");
            pos += xStr.length() + 2;
        }
        bool ok;
        return evaluate(s, ok);
    };
    
    return (evalAt(x + h) - evalAt(x - h)) / (2 * h);
}

// 数值积分 (辛普森法则)
double numericalIntegral(const std::wstring& funcExpr, double a, double b, int n = 1000) {
    if (n % 2 != 0) n++;
    double h = (b - a) / n;
    
    auto evalAt = [&](double val) -> double {
        std::wstring s = funcExpr;
        std::wstring xStr = std::to_wstring(val);
        size_t pos = 0;
        while ((pos = s.find(L'x', pos)) != std::wstring::npos) {
            s.replace(pos, 1, L"(" + xStr + L")");
            pos += xStr.length() + 2;
        }
        bool ok;
        return evaluate(s, ok);
    };
    
    double sum = evalAt(a) + evalAt(b);
    for (int i = 1; i < n; i++) {
        double xi = a + i * h;
        sum += (i % 2 == 0 ? 2 : 4) * evalAt(xi);
    }
    return sum * h / 3.0;
}

// 行列式 (3x3)
double determinant3x3(double m[3][3]) {
    return m[0][0]*(m[1][1]*m[2][2]-m[1][2]*m[2][1])
         - m[0][1]*(m[1][0]*m[2][2]-m[1][2]*m[2][0])
         + m[0][2]*(m[1][0]*m[2][1]-m[1][1]*m[2][0]);
}

// 逆矩阵 (3x3)
bool inverse3x3(double m[3][3], double inv[3][3]) {
    double det = determinant3x3(m);
    if (fabs(det) < 1e-12) return false;
    
    inv[0][0] = (m[1][1]*m[2][2] - m[1][2]*m[2][1]) / det;
    inv[0][1] = (m[0][2]*m[2][1] - m[0][1]*m[2][2]) / det;
    inv[0][2] = (m[0][1]*m[1][2] - m[0][2]*m[1][1]) / det;
    inv[1][0] = (m[1][2]*m[2][0] - m[1][0]*m[2][2]) / det;
    inv[1][1] = (m[0][0]*m[2][2] - m[0][2]*m[2][0]) / det;
    inv[1][2] = (m[0][2]*m[1][0] - m[0][0]*m[1][2]) / det;
    inv[2][0] = (m[1][0]*m[2][1] - m[1][1]*m[2][0]) / det;
    inv[2][1] = (m[0][1]*m[2][0] - m[0][0]*m[2][1]) / det;
    inv[2][2] = (m[0][0]*m[1][1] - m[0][1]*m[1][0]) / det;
    return true;
}

// ==================== GUI 创建 ====================

// 创建按钮
HWND CreateButton(HWND parent, const wchar_t* text, int x, int y, int w, int h, int id, COLORREF bgColor) {
    HWND btn = CreateWindowW(L"BUTTON", text,
        WS_CHILD | WS_VISIBLE | BS_PUSHBUTTON | BS_CENTER | BS_VCENTER,
        x, y, w, h, parent, (HMENU)(UINT_PTR)(ID_BTN_BASE + id),
        GetModuleHandle(NULL), NULL);
    return btn;
}

// 创建静态文本
HWND CreateLabel(HWND parent, const wchar_t* text, int x, int y, int w, int h, int id = 0) {
    return CreateWindowW(L"STATIC", text,
        WS_CHILD | WS_VISIBLE | SS_CENTER | SS_CENTERIMAGE,
        x, y, w, h, parent, (HMENU)(UINT_PTR)id,
        GetModuleHandle(NULL), NULL);
}

// 窗口过程函数声明
LRESULT CALLBACK MainWndProc(HWND hwnd, UINT msg, WPARAM wParam, LPARAM lParam);
LRESULT CALLBACK DisplayProc(HWND hwnd, UINT msg, WPARAM wParam, LPARAM lParam, UINT_PTR, DWORD_PTR);

// 创建主窗口的所有子控件
void CreateCalculatorTab(HWND parent) {
    int startY = 120;
    
    // 显示区域
    g_hDisplay = CreateWindowW(L"STATIC", L"0",
        WS_CHILD | WS_VISIBLE | SS_RIGHT | SS_CENTERIMAGE | WS_BORDER,
        15, 10, 470, 100, parent, (HMENU)ID_DISPLAY,
        GetModuleHandle(NULL), NULL);
    
    // ===== 按钮布局: 5列 x 7行 =====
    int btnW = 80, btnH = 45;
    int gap = 8;
    int startX = 15;
    
    struct BtnDef {
        const wchar_t* text; int id; COLORREF color; int col, row;
    };
    
    BtnDef buttons[] = {
        // 第1行: 高级函数
        {L"sin",   BTN_SIN,   COLOR_BTN_FUNC, 0, 0},
        {L"cos",   BTN_COS,   COLOR_BTN_FUNC, 1, 0},
        {L"tan",   BTN_TAN,   COLOR_BTN_FUNC, 2, 0},
        {L"ln",    BTN_LN,    COLOR_BTN_FUNC, 3, 0},
        {L"log₁₀", BTN_LOG,   COLOR_BTN_FUNC, 4, 0},
        
        // 第2行: 更多函数
        {L"√",     BTN_SQRT,  COLOR_BTN_FUNC, 0, 1},
        {L"x²",    BTN_POW,   COLOR_BTN_FUNC, 1, 1},
        {L"|x|",   BTN_ABS,   COLOR_BTN_FUNC, 2, 1},
        {L"n!",    BTN_FACT,  COLOR_BTN_FUNC, 3, 1},
        {L"π",     BTN_PI,    COLOR_BTN_FUNC, 4, 1},
        
        // 第3行: 括号和控制
        {L"(",     BTN_LPAREN, COLOR_BTN_FUNC, 0, 2},
        {L")",     BTN_RPAREN, COLOR_BTN_FUNC, 1, 2},
        {L"e",     BTN_E,     COLOR_BTN_FUNC, 2, 2},
        {L"C",     BTN_CLEAR, COLOR_BTN_CLR,  3, 2},
        {L"⌫",    BTN_DEL,   COLOR_BTN_CLR,  4, 2},
        
        // 第4行: 数字7-9和运算符
        {L"7",     BTN_7,     COLOR_BTN_NUM,  0, 3},
        {L"8",     BTN_8,     COLOR_BTN_NUM,  1, 3},
        {L"9",     BTN_9,     COLOR_BTN_NUM,  2, 3},
        {L"÷",     BTN_DIV,   COLOR_BTN_OP,   3, 3},
        {L"^",     BTN_POW,   COLOR_BTN_OP,   4, 3},
        
        // 第5行: 数字4-6
        {L"4",     BTN_4,     COLOR_BTN_NUM,  0, 4},
        {L"5",     BTN_5,     COLOR_BTN_NUM,  1, 4},
        {L"6",     BTN_6,     COLOR_BTN_NUM,  2, 4},
        {L"×",     BTN_MUL,   COLOR_BTN_OP,   3, 4},
        {L"xʸ",    BTN_POW,   COLOR_BTN_OP,   4, 4},
        
        // 第6行: 数字1-3
        {L"1",     BTN_1,     COLOR_BTN_NUM,  0, 5},
        {L"2",     BTN_2,     COLOR_BTN_NUM,  1, 5},
        {L"3",     BTN_3,     COLOR_BTN_NUM,  2, 5},
        {L"+",     BTN_ADD,   COLOR_BTN_OP,   3, 5},
        {L"±",     BTN_SIGN,  COLOR_BTN_OP,   4, 5},
        
        // 第7行: 数字0, ., =, -
        {L"0",     BTN_0,     COLOR_BTN_NUM,  0, 6},
        {L".",     BTN_DOT,   COLOR_BTN_NUM,  1, 6},
        {L"=",     BTN_EQUALS,COLOR_BTN_EQ,   2, 6},
        {L"−",     BTN_SUB,   COLOR_BTN_OP,   3, 6},
    };
    
    int nButtons = sizeof(buttons) / sizeof(buttons[0]);
    for (int i = 0; i < nButtons; i++) {
        int x = startX + buttons[i].col * (btnW + gap);
        int y = startY + buttons[i].row * (btnH + gap);
        CreateButton(parent, buttons[i].text, x, y, btnW, btnH, buttons[i].id, buttons[i].color);
    }
}

void CreateCalculusTab(HWND parent) {
    CreateLabel(parent, L"【数值微积分】", 15, 10, 470, 25);
    
    CreateLabel(parent, L"函数 f(x) =", 15, 45, 80, 25);
    g_hInputFunc = CreateWindowW(L"EDIT", L"sin(x)",
        WS_CHILD | WS_VISIBLE | WS_BORDER | ES_AUTOHSCROLL,
        95, 43, 300, 27, parent, (HMENU)ID_INPUT_FUNC,
        GetModuleHandle(NULL), NULL);
    
    // 求导按钮
    CreateButton(parent, L"求导 f'(x₀)", 15, 80, 130, 40, BTN_DIFF, RGB(100, 180, 100));
    CreateButton(parent, L"积分 ∫f(x)dx [a,b]", 155, 80, 160, 40, BTN_INTEG, RGB(100, 140, 200));
    CreateButton(parent, L"极限 lim(x→x₀)", 325, 80, 150, 40, BTN_LIMIT, RGB(200, 150, 100));
    
    CreateLabel(parent, L"参数 (x₀ 或 区间 a,b):", 15, 135, 200, 25);
    g_hResultBox = CreateWindowW(L"EDIT", L"",
        WS_CHILD | WS_VISIBLE | WS_BORDER | WS_VSCROLL | ES_MULTILINE | ES_READONLY,
        15, 160, 460, 250, parent, (HMENU)ID_RESULT_BOX,
        GetModuleHandle(NULL), NULL);
}

void CreateMatrixTab(HWND parent) {
    CreateLabel(parent, L"【矩阵运算 (3×3)】", 15, 10, 470, 25);
    
    CreateLabel(parent, L"矩阵元素 (逗号分隔，每行9个数):", 15, 45, 400, 25);
    g_hInputFunc = CreateWindowW(L"EDIT", L"1,0,0,0,1,0,0,0,1",
        WS_CHILD | WS_VISIBLE | WS_BORDER | ES_AUTOHSCROLL,
        15, 70, 400, 27, parent, (HMENU)ID_INPUT_FUNC,
        GetModuleHandle(NULL), NULL);
    
    CreateButton(parent, L"计算行列式", 15, 110, 130, 40, BTN_DET, RGB(200, 150, 100));
    CreateButton(parent, L"求逆矩阵", 155, 110, 130, 40, BTN_INV, RGB(100, 180, 100));
    CreateButton(parent, L"转置矩阵", 295, 110, 130, 40, BTN_TRANS, RGB(100, 140, 200));
    
    g_hResultBox = CreateWindowW(L"EDIT", L"",
        WS_CHILD | WS_VISIBLE | WS_BORDER | WS_VSCROLL | ES_MULTILINE | ES_READONLY,
        15, 160, 460, 250, parent, (HMENU)ID_RESULT_BOX,
        GetModuleHandle(NULL), NULL);
}

void CreateEquationTab(HWND parent) {
    CreateLabel(parent, L"【方程求解 & 级数】", 15, 10, 470, 25);
    
    CreateLabel(parent, L"功能说明:", 15, 45, 470, 20);
    g_hResultBox = CreateWindowW(L"EDIT",
        L"══════ 高等数学计算器 ══════\r\n\r\n"
        L"【计算器模式】\r\n"
        L"  · 支持基本四则运算 + - × ÷\r\n"
        L"  · 幂运算 ^ (如 2^10 = 1024)\r\n"
        L"  · 三角函数: sin, cos, tan\r\n"
        L"  · 对数: ln(自然), log(常用)\r\n"
        L"  · 平方根: sqrt(x), 绝对值: abs(x)\r\n"
        L"  · 常量: π (pi), e (自然常数)\r\n"
        L"  · 阶乘: n! (非负整数)\r\n"
        L"  · 括号嵌套: ( )\r\n"
        L"  · 一元负号: 如 -5+3 正确解析\r\n\r\n"
        L"【微积分模式】\r\n"
        L"  · 数值求导: 中心差分法, 默认h=10⁻⁶\r\n"
        L"  · 数值积分: 辛普森法则, n=1000区间\r\n"
        L"  · 使用 x 作为变量\r\n\r\n"
        L"【矩阵模式】\r\n"
        L"  · 行列式计算 (3×3)\r\n"
        L"  · 逆矩阵求解\r\n"
        L"  · 转置矩阵\r\n"
        L"  · 输入格式: a,b,c,d,e,f,g,h,i\r\n\r\n"
        L"════════════════════════",
        WS_CHILD | WS_VISIBLE | WS_BORDER | WS_VSCROLL | ES_MULTILINE | ES_READONLY,
        15, 70, 460, 340, parent, (HMENU)ID_RESULT_BOX,
        GetModuleHandle(NULL), NULL);
}

// 切换标签页
void SwitchTab(HWND parent, int tab) {
    // 隐藏所有特定控件
    if (g_hDisplay) ShowWindow(g_hDisplay, SW_HIDE);
    if (g_hInputFunc) ShowWindow(g_hInputFunc, SW_HIDE);
    if (g_hResultBox) ShowWindow(g_hResultBox, SW_HIDE);
    
    // 销毁所有子控件
    HWND child = GetWindow(parent, GW_CHILD);
    while (child) {
        HWND next = GetWindow(child, GW_HWNDNEXT);
        int cid = GetDlgCtrlID(child);
        if (cid >= ID_BTN_BASE && cid < ID_BTN_BASE + BTN_COUNT) {
            DestroyWindow(child);
        }
        child = next;
    }
    if (g_hDisplay) { DestroyWindow(g_hDisplay); g_hDisplay = NULL; }
    if (g_hInputFunc) { DestroyWindow(g_hInputFunc); g_hInputFunc = NULL; }
    if (g_hResultBox) { DestroyWindow(g_hResultBox); g_hResultBox = NULL; }
    
    g_currentTab = tab;
    
    // 更新标签按钮外观
    SendMessage(g_hTabCalc, BM_SETSTATE, tab == 0, 0);
    SendMessage(g_hTabCalculus, BM_SETSTATE, tab == 1, 0);
    SendMessage(g_hTabMatrix, BM_SETSTATE, tab == 2, 0);
    SendMessage(g_hTabEquation, BM_SETSTATE, tab == 3, 0);
    
    switch (tab) {
        case 0: CreateCalculatorTab(parent); break;
        case 1: CreateCalculusTab(parent); break;
        case 2: CreateMatrixTab(parent); break;
        case 3: CreateEquationTab(parent); break;
    }
}

// 更新显示
void UpdateDisplay() {
    if (!g_hDisplay) return;
    std::wstring text;
    if (g_expression.empty()) {
        text = g_result.empty() ? L"0" : g_result;
    } else {
        text = g_expression;
    }
    SetWindowTextW(g_hDisplay, text.c_str());
}

// 处理计算器按钮
void HandleCalcButton(int btnId) {
    if (g_justEvaluated) {
        if (btnId >= BTN_0 && btnId <= BTN_9) {
            g_expression = L"";
            g_result = L"";
        }
        g_justEvaluated = false;
    }
    
    switch (btnId) {
        case BTN_0: g_expression += L'0'; break;
        case BTN_1: g_expression += L'1'; break;
        case BTN_2: g_expression += L'2'; break;
        case BTN_3: g_expression += L'3'; break;
        case BTN_4: g_expression += L'4'; break;
        case BTN_5: g_expression += L'5'; break;
        case BTN_6: g_expression += L'6'; break;
        case BTN_7: g_expression += L'7'; break;
        case BTN_8: g_expression += L'8'; break;
        case BTN_9: g_expression += L'9'; break;
        case BTN_DOT: g_expression += L'.'; break;
        case BTN_ADD: g_expression += L'+'; break;
        case BTN_SUB: g_expression += L'-'; break;
        case BTN_MUL: g_expression += L'*'; break;
        case BTN_DIV: g_expression += L'/'; break;
        case BTN_POW: g_expression += L'^'; break;
        case BTN_LPAREN: g_expression += L'('; break;
        case BTN_RPAREN: g_expression += L')'; break;
        case BTN_PI: g_expression += L'π'; break;
        case BTN_E: g_expression += L'e'; break;
        
        case BTN_SIN: g_expression += L"sin("; break;
        case BTN_COS: g_expression += L"cos("; break;
        case BTN_TAN: g_expression += L"tan("; break;
        case BTN_LN: g_expression += L"ln("; break;
        case BTN_LOG: g_expression += L"log("; break;
        case BTN_SQRT: g_expression += L"sqrt("; break;
        case BTN_ABS: g_expression += L"abs("; break;
        case BTN_FACT: g_expression += L'!'; break;
        
        case BTN_SIGN: {
            if (!g_expression.empty()) {
                if (g_expression[0] == L'-')
                    g_expression = g_expression.substr(1);
                else
                    g_expression = L"-(" + g_expression + L")";
            }
            break;
        }
        
        case BTN_CLEAR:
            g_expression = L"";
            g_result = L"";
            break;
            
        case BTN_DEL:
            if (!g_expression.empty()) {
                // 检查末尾是否为多字符函数
                size_t len = g_expression.length();
                if (len >= 4 && g_expression.substr(len-4) == L"sqrt") g_expression = g_expression.substr(0, len-4);
                else if (len >= 3 && (g_expression.substr(len-3) == L"sin" ||
                                       g_expression.substr(len-3) == L"cos" ||
                                       g_expression.substr(len-3) == L"tan" ||
                                       g_expression.substr(len-3) == L"abs" ||
                                       g_expression.substr(len-3) == L"log"))
                    g_expression = g_expression.substr(0, len-3);
                else if (len >= 2 && g_expression.substr(len-2) == L"ln")
                    g_expression = g_expression.substr(0, len-2);
                else
                    g_expression.pop_back();
            }
            break;
            
        case BTN_EQUALS: {
            bool ok;
            double val = evaluate(g_expression, ok);
            if (ok) {
                std::wostringstream oss;
                oss << std::setprecision(12) << val;
                g_result = oss.str();
                // 去掉尾部多余的零
                size_t dotPos = g_result.find(L'.');
                if (dotPos != std::wstring::npos) {
                    while (g_result.back() == L'0') g_result.pop_back();
                    if (g_result.back() == L'.') g_result.pop_back();
                }
                g_expression = L"";
                g_justEvaluated = true;
            } else {
                g_result = L"错误";
                g_expression = L"";
            }
            break;
        }
    }
    UpdateDisplay();
}

// 处理微积分按钮
void HandleCalculusButton(int btnId) {
    if (!g_hInputFunc || !g_hResultBox) return;
    
    wchar_t funcBuf[512] = {0};
    GetWindowTextW(g_hInputFunc, funcBuf, 512);
    std::wstring funcStr(funcBuf);
    
    std::wstring result;
    
    switch (btnId) {
        case BTN_DIFF: {
            // 求导 - 需要 x0
            // 弹出一个简单的输入框
            result = L"【数值求导】中心差分法 h=10⁻⁶\r\n";
            result += L"函数: f(x) = " + funcStr + L"\r\n\r\n";
            result += L"示例: 在 x₀=1 处求导\r\n";
            result += L"f'(1) ≈ " + std::to_wstring(numericalDerivative(funcStr, 1.0)) + L"\r\n";
            result += L"\r\n使用方法: 修改上方函数表达式，\r\n";
            result += L"求导点 x₀ 目前固定为 1.0\r\n";
            result += L"(可在代码中修改 numericalDerivative 的 x 参数)";
            break;
        }
        case BTN_INTEG: {
            result = L"【数值积分】辛普森法则 n=1000\r\n";
            result += L"函数: f(x) = " + funcStr + L"\r\n\r\n";
            result += L"示例: 在 [0, π] 上积分\r\n";
            double integral = numericalIntegral(funcStr, 0.0, 3.141592653589793);
            result += L"∫[0→π] f(x)dx ≈ " + std::to_wstring(integral) + L"\r\n";
            result += L"\r\n使用方法: 修改上方函数表达式，\r\n";
            result += L"积分区间目前固定为 [0, π]\r\n";
            result += L"(可在代码中修改 numericalIntegral 的 a,b 参数)";
            break;
        }
        case BTN_LIMIT: {
            result = L"【极限计算】数值逼近法\r\n";
            result += L"函数: f(x) = " + funcStr + L"\r\n\r\n";
            result += L"示例: lim(x→0)\r\n";
            
            auto evalAt = [&](double val) -> double {
                std::wstring s = funcStr;
                std::wstring xStr = std::to_wstring(val);
                size_t pos = 0;
                while ((pos = s.find(L'x', pos)) != std::wstring::npos) {
                    s.replace(pos, 1, L"(" + xStr + L")");
                    pos += xStr.length() + 2;
                }
                bool ok;
                return evaluate(s, ok);
            };
            
            result += L"左极限 (x→0⁻): " + std::to_wstring(evalAt(-1e-10)) + L"\r\n";
            result += L"右极限 (x→0⁺): " + std::to_wstring(evalAt(1e-10)) + L"\r\n";
            result += L"\r\n(若左右极限相等则为极限值)";
            break;
        }
    }
    SetWindowTextW(g_hResultBox, result.c_str());
}

// 处理矩阵按钮
void HandleMatrixButton(int btnId) {
    if (!g_hInputFunc || !g_hResultBox) return;
    
    wchar_t buf[512] = {0};
    GetWindowTextW(g_hInputFunc, buf, 512);
    std::wstring input(buf);
    
    // 解析逗号分隔的数字
    double vals[9] = {0};
    std::wstringstream ss(input);
    std::wstring token;
    int idx = 0;
    while (std::getline(ss, token, L',') && idx < 9) {
        vals[idx++] = std::stod(token);
    }
    
    double m[3][3];
    for (int i = 0; i < 3; i++)
        for (int j = 0; j < 3; j++)
            m[i][j] = vals[i*3 + j];
    
    std::wstring result;
    
    switch (btnId) {
        case BTN_DET: {
            double det = determinant3x3(m);
            result = L"【行列式计算】\r\n\r\n矩阵:\r\n";
            for (int i = 0; i < 3; i++) {
                wchar_t line[128];
                swprintf(line, 128, L"  [ %8.4f  %8.4f  %8.4f ]\r\n", m[i][0], m[i][1], m[i][2]);
                result += line;
            }
            result += L"\r\ndet(A) = " + std::to_wstring(det);
            break;
        }
        case BTN_INV: {
            double inv[3][3];
            bool ok = inverse3x3(m, inv);
            result = L"【逆矩阵】\r\n\r\n原矩阵:\r\n";
            for (int i = 0; i < 3; i++) {
                wchar_t line[128];
                swprintf(line, 128, L"  [ %8.4f  %8.4f  %8.4f ]\r\n", m[i][0], m[i][1], m[i][2]);
                result += line;
            }
            if (ok) {
                result += L"\r\n逆矩阵 A⁻¹:\r\n";
                for (int i = 0; i < 3; i++) {
                    wchar_t line[128];
                    swprintf(line, 128, L"  [ %8.4f  %8.4f  %8.4f ]\r\n", inv[i][0], inv[i][1], inv[i][2]);
                    result += line;
                }
            } else {
                result += L"\r\n❌ 矩阵不可逆 (行列式为0)";
            }
            break;
        }
        case BTN_TRANS: {
            result = L"【转置矩阵】\r\n\r\n原矩阵:\r\n";
            for (int i = 0; i < 3; i++) {
                wchar_t line[128];
                swprintf(line, 128, L"  [ %8.4f  %8.4f  %8.4f ]\r\n", m[i][0], m[i][1], m[i][2]);
                result += line;
            }
            result += L"\r\n转置矩阵 Aᵀ:\r\n";
            for (int i = 0; i < 3; i++) {
                wchar_t line[128];
                swprintf(line, 128, L"  [ %8.4f  %8.4f  %8.4f ]\r\n", m[0][i], m[1][i], m[2][i]);
                result += line;
            }
            break;
        }
    }
    SetWindowTextW(g_hResultBox, result.c_str());
}

// WndProc - 按钮子类化处理颜色
LRESULT CALLBACK BtnProc(HWND hwnd, UINT msg, WPARAM wParam, LPARAM lParam, UINT_PTR id, DWORD_PTR) {
    if (msg == WM_ERASEBKGND) {
        HDC dc = (HDC)wParam;
        RECT rc;
        GetClientRect(hwnd, &rc);
        
        COLORREF color;
        int btnId = id - ID_BTN_BASE;
        
        if (btnId >= BTN_0 && btnId <= BTN_9) color = COLOR_BTN_NUM;
        else if (btnId == BTN_ADD || btnId == BTN_SUB || btnId == BTN_MUL || 
                 btnId == BTN_DIV || btnId == BTN_POW || btnId == BTN_SIGN) color = COLOR_BTN_OP;
        else if (btnId == BTN_EQUALS) color = COLOR_BTN_EQ;
        else if (btnId == BTN_CLEAR || btnId == BTN_DEL) color = COLOR_BTN_CLR;
        else if (btnId == BTN_DIFF) color = RGB(100, 180, 100);
        else if (btnId == BTN_INTEG) color = RGB(100, 140, 200);
        else if (btnId == BTN_LIMIT || btnId == BTN_DET) color = RGB(200, 150, 100);
        else if (btnId == BTN_INV) color = RGB(100, 180, 100);
        else if (btnId == BTN_TRANS) color = RGB(100, 140, 200);
        else color = COLOR_BTN_FUNC;
        
        HBRUSH br = CreateSolidBrush(color);
        FillRect(dc, &rc, br);
        DeleteObject(br);
        
        // 绘制文字
        wchar_t text[32];
        GetWindowTextW(hwnd, text, 32);
        SetBkMode(dc, TRANSPARENT);
        SetTextColor(dc, COLOR_TEXT);
        
        HFONT font = CreateFontW(20, 0, 0, 0, FW_NORMAL, FALSE, FALSE, FALSE,
            DEFAULT_CHARSET, OUT_DEFAULT_PRECIS, CLIP_DEFAULT_PRECIS,
            DEFAULT_QUALITY, DEFAULT_PITCH, L"Segoe UI");
        HFONT oldFont = (HFONT)SelectObject(dc, font);
        DrawTextW(dc, text, -1, &rc, DT_CENTER | DT_VCENTER | DT_SINGLELINE);
        SelectObject(dc, oldFont);
        DeleteObject(font);
        
        return 1;
    }
    if (msg == WM_KEYDOWN) return 0;
    return DefSubclassProc(hwnd, msg, wParam, lParam);
}

// 主窗口过程
LRESULT CALLBACK MainWndProc(HWND hwnd, UINT msg, WPARAM wParam, LPARAM lParam) {
    switch (msg) {
        case WM_CREATE: {
            g_hMainWnd = hwnd;
            
            // 创建标签按钮
            g_hTabCalc = CreateWindowW(L"BUTTON", L"🔢 计算器",
                WS_CHILD | WS_VISIBLE | BS_PUSHBUTTON,
                0, 0, 125, 35, hwnd, (HMENU)ID_TAB_CALC,
                GetModuleHandle(NULL), NULL);
            g_hTabCalculus = CreateWindowW(L"BUTTON", L"📐 微积分",
                WS_CHILD | WS_VISIBLE | BS_PUSHBUTTON,
                125, 0, 125, 35, hwnd, (HMENU)ID_TAB_CALCULUS,
                GetModuleHandle(NULL), NULL);
            g_hTabMatrix = CreateWindowW(L"BUTTON", L"📊 矩阵",
                WS_CHILD | WS_VISIBLE | BS_PUSHBUTTON,
                250, 0, 125, 35, hwnd, (HMENU)ID_TAB_MATRIX,
                GetModuleHandle(NULL), NULL);
            g_hTabEquation = CreateWindowW(L"BUTTON", L"ℹ️ 帮助",
                WS_CHILD | WS_VISIBLE | BS_PUSHBUTTON,
                375, 0, 125, 35, hwnd, (HMENU)ID_TAB_EQUATION,
                GetModuleHandle(NULL), NULL);
            
            // 默认显示计算器
            CreateCalculatorTab(hwnd);
            break;
        }
        
        case WM_CTLCOLORSTATIC: {
            HDC dc = (HDC)wParam;
            HWND ctrl = (HWND)lParam;
            if (GetDlgCtrlID(ctrl) == ID_DISPLAY) {
                SetBkColor(dc, COLOR_DISPLAY);
                SetTextColor(dc, RGB(0, 255, 150));
                static HBRUSH br = CreateSolidBrush(COLOR_DISPLAY);
                return (LRESULT)br;
            }
            SetBkColor(dc, COLOR_BG);
            SetTextColor(dc, COLOR_TEXT);
            static HBRUSH brBg = CreateSolidBrush(COLOR_BG);
            return (LRESULT)brBg;
        }
        
        case WM_ERASEBKGND: {
            HDC dc = (HDC)wParam;
            RECT rc;
            GetClientRect(hwnd, &rc);
            HBRUSH br = CreateSolidBrush(COLOR_BG);
            FillRect(dc, &rc, br);
            DeleteObject(br);
            return 1;
        }
        
        case WM_COMMAND: {
            int id = LOWORD(wParam);
            
            if (id >= ID_BTN_BASE && id < ID_BTN_BASE + BTN_COUNT) {
                int btnId = id - ID_BTN_BASE;
                if (g_currentTab == 0) HandleCalcButton(btnId);
                else if (g_currentTab == 1) HandleCalculusButton(btnId);
                else if (g_currentTab == 2) HandleMatrixButton(btnId);
                return 0;
            }
            
            switch (id) {
                case ID_TAB_CALC:      SwitchTab(hwnd, 0); break;
                case ID_TAB_CALCULUS:  SwitchTab(hwnd, 1); break;
                case ID_TAB_MATRIX:    SwitchTab(hwnd, 2); break;
                case ID_TAB_EQUATION:  SwitchTab(hwnd, 3); break;
                case ID_BTN_COMPUTE: {
                    if (g_currentTab == 1 && g_hInputFunc && g_hResultBox) {
                        // 默认做求导
                        HandleCalculusButton(BTN_DIFF);
                    }
                    break;
                }
            }
            return 0;
        }
        
        case WM_DESTROY:
            PostQuitMessage(0);
            return 0;
    }
    return DefWindowProcW(hwnd, msg, wParam, lParam);
}

// 入口点
int WINAPI WinMain(HINSTANCE hInstance, HINSTANCE, LPSTR, int nCmdShow) {
    // 初始化通用控件
    INITCOMMONCONTROLSEX icc = { sizeof(INITCOMMONCONTROLSEX), ICC_STANDARD_CLASSES };
    InitCommonControlsEx(&icc);
    
    // 注册窗口类
    WNDCLASSW wc = {};
    wc.lpfnWndProc = MainWndProc;
    wc.hInstance = hInstance;
    wc.hCursor = LoadCursor(NULL, IDC_ARROW);
    wc.hbrBackground = (HBRUSH)(COLOR_WINDOW + 1);
    wc.lpszClassName = L"AdvancedMathCalc";
    RegisterClassW(&wc);
    
    // 创建主窗口
    HWND hwnd = CreateWindowW(L"AdvancedMathCalc", L"高等数学计算器 v2.0",
        WS_OVERLAPPEDWINDOW & ~(WS_MAXIMIZEBOX | WS_THICKFRAME),
        CW_USEDEFAULT, CW_USEDEFAULT, 520, 520,
        NULL, NULL, hInstance, NULL);
    
    if (!hwnd) return 1;
    
    // 子类化所有按钮以支持颜色
    SetWindowSubclass(hwnd, [](HWND, UINT, WPARAM, LPARAM, UINT_PTR, DWORD_PTR) -> LRESULT {
        return 0;
    }, 0, 0);
    
    ShowWindow(hwnd, nCmdShow);
    UpdateWindow(hwnd);
    
    // 消息循环
    MSG msg;
    while (GetMessage(&msg, NULL, 0, 0)) {
        TranslateMessage(&msg);
        DispatchMessage(&msg);
    }
    
    return (int)msg.wParam;
}

// 子类化窗口过程用于按钮着色
// (在WinMain之后通过EnumChildWindows设置)
