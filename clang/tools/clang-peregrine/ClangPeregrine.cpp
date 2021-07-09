#include "clang/Tooling/CommonOptionsParser.h"
#include "clang/Frontend/FrontendActions.h"
#include "clang/Tooling/Tooling.h"
#include <iostream>
#include "clang/AST/AST.h"
#include "clang/AST/DeclObjC.h"
#include "clang/AST/ASTConsumer.h"
#include "clang/ASTMatchers/ASTMatchers.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/Frontend/FrontendPluginRegistry.h"
#include "clang/Rewrite/Core/Rewriter.h"
#include "clang/jsoncpp/jsoncpp.cpp"
#include <fstream>
#include <string.h>
#include <stdarg.h>
#include <sys/stat.h>

using namespace clang;
using namespace std;
using namespace llvm;
using namespace clang::ast_matchers;
using namespace clang::tooling;

std::string outputPath;

struct RouterStruct {
    RouterStruct() : URL() {}
    RouterStruct(std::string S, std::string I, std::string B)
    : URL(S), CLASS(I), SELECT(B) {}
    std::string URL;
    std::string CLASS;
    std::string SELECT;
};

std::vector<RouterStruct> routers;

static void appendRouterToFile(std::vector<RouterStruct> routers) {
    if (routers.size() > 0) {
        mkdir(outputPath.c_str(), 0775);
        std::string filePath = outputPath + "/routers.json";
        printf("%s", filePath.c_str());
        llvm::errs() << filePath << "\n";
        ifstream inFile(filePath);
        std::string OLDS((std::istreambuf_iterator<char>(inFile)),
                         std::istreambuf_iterator<char>());
        inFile.close();
        Json::Reader reader;
        Json::Value root;
        reader.parse(OLDS, root);
        
        vector<RouterStruct>::iterator it;
        for(it=routers.begin();it!=routers.end();it++) {
            RouterStruct R = *it;
            for (unsigned int i = 0; i < root.size(); i++) {
                Json::Value item = root[i];
                if (item["url"].asString() == R.URL) {
                    root.removeIndex(i, &item);
                    break;
                }
            }
            
            Json::Value newValue;
            newValue["url"] = R.URL;
            newValue["class"] = R.CLASS;
            newValue["selector"] = R.SELECT;
            root.append(newValue);
        }
        
        std::ofstream outFile(filePath, ios::out | ios::trunc);
        outFile << root.toStyledString();
        outFile.close();
        routers.clear();
    }
}

bool isUserSourceCode(const string filename) {
    if (filename.empty()) return false;
    // 非Xcode中的源码都认为是用户源码
    size_t t = filename.find("/Applications/Xcode");
    return t == string::npos;
}

namespace PeregrinePlugin {
    class QTMatchHandler: public MatchFinder::MatchCallback {
        private:
        bool isShouldUseCopy(const string typeStr) {
            if (typeStr.find("NSString") != string::npos ||
                typeStr.find("NSArray") != string::npos ||
                typeStr.find("NSDictionary") != string::npos/*...*/) {
                return true;
            }
            return false;
        }
        public:
        QTMatchHandler(CompilerInstance &CI) {
        }
        
        void run(const MatchFinder::MatchResult &Result) {
            const ObjCImplementationDecl *ID =  Result.Nodes.getNodeAs<ObjCImplementationDecl>("objcDecl");
            for(auto method = ID->classmeth_begin();method!=ID->classmeth_end();method++) {
                const auto ocmd = *method;
                handleObjcMethDecl(ocmd);
            }
            return;
            const ObjCMethodDecl *MD = Result.Nodes.getNodeAs<ObjCMethodDecl>("objcMethodDecl");
            handleObjcMethDecl(MD);
        }
        
        bool handleObjcMethDecl(const ObjCMethodDecl *MD) {
            if (MD->hasAttr<RoutableAttr>()) {
                DiagnosticsEngine &diag = MD->getASTContext().getDiagnostics();
                RoutableAttr *targetAttr = MD->getAttr<RoutableAttr>();
                                
                if (MD->isInstanceMethod()) {
                    FixItHint fixHint = FixItHint::CreateReplacement(MD->getSelectorStartLoc(), "+");
                    diag.Report(MD->getSelectorStartLoc(), diag.getCustomDiagID(DiagnosticsEngine::Error, "Should not be instance method.")) << fixHint;
                }
                
                //返回值
                bool valid = true;
                QualType returnType = MD->getReturnType();
                if (returnType.getAsString().find("void") == std::string::npos) {
                    valid = false;
                    FixItHint fixHint = FixItHint::CreateReplacement(MD->getReturnTypeSourceRange(), "void");
                    diag.Report(MD->getReturnTypeSourceRange().getBegin().getLocWithOffset(1), diag.getCustomDiagID(DiagnosticsEngine::Warning, "Should not return a value")) << MD->getReturnType().getAsString() << fixHint;
                }
                
                if (MD->param_size() == 0) {
                    SourceLocation insertLoc = MD->getSelectorLoc(0).getLocWithOffset(MD->getDeclName().getAsString().size());
                    FixItHint hint = FixItHint::CreateInsertion(insertLoc, ":(RouteContext *)context");
                    diag.Report(insertLoc, diag.getCustomDiagID(DiagnosticsEngine::Error, "At least one parameter  need of type RouteContext *")) << hint;
                } else {
                    //参数1类型
                    const ParmVarDecl *paramDecl1 = MD->getParamDecl(0);
                    if (paramDecl1->getType().getAsString().find("RouteContext") == std::string::npos) {
                        valid = false;
                        FixItHint fixHint = FixItHint::CreateReplacement(paramDecl1->getTypeSpecStartLoc(), "PGRouterContext");
                        diag.Report(paramDecl1->getLocation(), diag.getCustomDiagID(DiagnosticsEngine::Warning, "Incompatible pointer types sending 'RouteContext *' to parameter of type '%0'")) << paramDecl1->getType().getAsString() << fixHint;
                    }
                    
                    if (MD->param_size() > 1) {
                        SourceLocation insertLoc = paramDecl1->getEndLoc().getLocWithOffset(paramDecl1->getName().size());
                        diag.Report(insertLoc, diag.getCustomDiagID(DiagnosticsEngine::Warning, "Supports only one parameter at most"));
                    }
                }
                
                if (valid) {//路由定义有效
                    llvm::errs() << "🍺Did find router config: " << targetAttr->getUrl().str() << "\n";
                    std::string url = targetAttr->getUrl().str();
                    std::string className = MD->getClassInterface()->getName().str();
                    std::string selector = MD->getSelector().getAsString();
                    RouterStruct routerS = {url, className, selector};
                    routers.push_back(routerS);
                }
            }
            return true;
        }
        
    };
    
    class QTASTConsumer: public ASTConsumer {
        private:
        MatchFinder matcher;
        QTMatchHandler handler;
        public:
        QTASTConsumer(CompilerInstance &CI) :handler(CI) {
            matcher.addMatcher(objcImplementationDecl().bind("objcDecl"), &handler);
//            matcher.addMatcher(objcMethodDecl().bind("objcMethodDecl"), &handler);
        }
        
        void HandleTranslationUnit(ASTContext &context) {
            matcher.matchAST(context);
        }
    };
    
    class ClangPeregrineAction: public ASTFrontendAction {
        private:
        StringRef curFile;
        public:
        unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &CI, StringRef iFile) override {
            if(isUserSourceCode(iFile.str())) {
                return unique_ptr<QTASTConsumer> (new QTASTConsumer(CI));
            }
            return NULL;
        }
    };
}

//static FrontendPluginRegistry::Add<PeregrinePlugin::PeregrineASTAction> X("PeregrinePlugin", "PeregrinePlugin is a tool for generator router table.");


#pragma mark 入口

static cl::OptionCategory OptsCategory("ClangPeregrine", "Router Generator");

static bool startsWith(const char *pre, const char *str)
{
    if (str == NULL) return false;
    size_t lenpre = strlen(pre),
    lenstr = strlen(str);
    return lenstr < lenpre ? false : strncmp(pre, str, lenpre) == 0;
}

int main(int argc, const char **argv) {
    outputPath = ".";
#if 1
    printf("-------------------------\n");
    for (int i=0; i < argc; i++) {
        const char *param = argv[i];
        printf("argv[%d] = \"%s\";\n", i, param);
        if (param == NULL) {
            continue;
        }
        if (startsWith("-p=", param)) {
            string str(param);
            outputPath = str.substr(3);
        }
    }
    printf("-------------------------\n");
#endif
    auto ExpectedParser =
        CommonOptionsParser::create(argc, argv, OptsCategory);
    if (!ExpectedParser) {
      llvm::errs() << ExpectedParser.takeError();
      return 1;
    }
    CommonOptionsParser &op = ExpectedParser.get();
    ClangTool Tool(op.getCompilations(), op.getSourcePathList());
    int result = Tool.run(newFrontendActionFactory<PeregrinePlugin::ClangPeregrineAction>().get());
    printf("route count: %lu\n", routers.size());
    appendRouterToFile(routers);
    return result;
}
